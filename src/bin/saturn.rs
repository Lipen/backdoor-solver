use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::process;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Instant;

use backdoor::derivation::derive_clauses;
use backdoor::lit::Lit;
use backdoor::searcher::{BackdoorSearcher, Options, DEFAULT_OPTIONS};
use backdoor::solvers::SatSolver;
use backdoor::trie::Trie;
use backdoor::utils::*;
use backdoor::var::Var;

use cadical::statik::Cadical;
use cadical::{LitValue, SolveResponse};

use clap::Parser;
use crossbeam_channel::{unbounded, Receiver, Select, Sender, TryRecvError};
use indicatif::{ProgressBar, ProgressIterator, ProgressStyle};
use itertools::{iproduct, zip_eq, Itertools};
use log::{debug, info};
use ordered_float::OrderedFloat;
use rand::prelude::*;

#[derive(Parser, Debug, Clone)]
#[command(author, version, about = "SAT Solver with Backdoor Search")]
struct Cli {
    /// Input file with CNF in DIMACS format.
    #[arg(value_name = "CNF")]
    path_cnf: PathBuf,

    /// Path to a file with results.
    #[arg(long = "results", value_name = "FILE")]
    path_results: Option<PathBuf>,

    /// Random seed.
    #[arg(long, value_name = "INT", default_value_t = 42)]
    seed: u64,

    /// Number of derivers.
    #[arg(short = 't', value_name = "INT", default_value_t = 1)]
    num_derivers: usize,

    /// Backdoor size.
    #[arg(long, value_name = "INT")]
    backdoor_size: usize,

    /// Number of EA iterations.
    #[arg(long, value_name = "INT")]
    num_iters: usize,

    /// Number of stagnated iterations before re-initialization.
    #[arg(long, value_name = "INT")]
    stagnation_limit: Option<usize>,

    /// Timeout for each EA run (in seconds).
    #[arg(long, value_name = "FLOAT")]
    run_timeout: Option<f64>,

    /// Do ban variables used in the best backdoors on previous runs?
    #[arg(long)]
    ban_used: bool,

    /// Do not derive clauses.
    #[arg(long)]
    no_derive: bool,

    /// Derive ternary clauses.
    #[arg(long)]
    derive_ternary: bool,

    /// Maximum product size.
    #[arg(long, value_name = "INT", default_value_t = 100000)]
    max_product: usize,

    /// Use novel sorted filtering method.
    #[arg(long)]
    use_sorted_filtering: bool,

    /// Number of conflicts (budget per task in filtering).
    #[arg(long, value_name = "INT", default_value_t = 1000)]
    num_conflicts: usize,

    /// Initial budget (in conflicts) for filtering.
    #[arg(long, value_name = "INT")]
    budget_filter: u64,

    /// Multiplicative factor for filtering budget.
    #[arg(long, value_name = "FLOAT", default_value_t = 1.0)]
    factor_budget_filter: f64,

    /// Initial conflicts budget for solving.
    #[arg(long, value_name = "INT", default_value_t = 10000)]
    budget_solve: u64,

    /// Multiplicative factor for solving budget.
    #[arg(long, value_name = "FLOAT", default_value_t = 1.0)]
    factor_budget_solve: f64,

    /// Budget (in conflicts) for pre-solve.
    #[arg(long, value_name = "INT", default_value_t = 0)]
    budget_presolve: u64,

    /// Path to a file with proof.
    #[arg(long = "proof", value_name = "FILE")]
    path_proof: Option<PathBuf>,

    /// Write non-binary proof.
    #[arg(long)]
    proof_no_binary: bool,

    /// Comma-separated list of Cadical options ('key=value' pairs, e.g. 'elim=0,ilb=0,check=1').
    #[arg(long)]
    cadical_options: Option<String>,

    /// Comma-separated list of allowed variables (1-based indices).
    #[arg(long = "allow", value_name = "INT...")]
    allowed_vars: Option<String>,

    /// Comma-separated list of banned variables (1-based indices).
    #[arg(long = "ban", value_name = "INT...")]
    banned_vars: Option<String>,

    /// Do not print solver stats in the end.
    #[arg(long)]
    no_stats: bool,
}

// Result of the SAT solver
#[allow(unused)]
enum SolveResult {
    SAT, // TODO: model
    UNSAT,
    UNKNOWN,
}

// Messages for communication between actors
#[derive(Debug, Clone)]
enum Message {
    DerivedClause(Vec<Lit>),
    LearnedClause(Vec<Lit>),
    Terminate,
}

// Actor responsible for the searcher
struct SearcherActor {
    tx_derived_clauses: Sender<Message>,
    rx_learned_clauses: Receiver<Message>,
    cli: Cli,
    searcher: BackdoorSearcher,
    all_clauses: HashSet<Vec<Lit>>,
    finish: Arc<AtomicBool>,
}

impl SearcherActor {
    fn new(
        tx_derived_clauses: Sender<Message>,
        rx_learned_clauses: Receiver<Message>,
        cli: Cli,
        finish: Arc<AtomicBool>,
        seed: u64,
    ) -> Self {
        let mut all_clauses: HashSet<Vec<Lit>> = HashSet::new();
        for mut clause in parse_dimacs(&cli.path_cnf) {
            clause.sort_by_key(|lit| lit.inner());
            all_clauses.insert(clause);
        }
        info!("Original clauses: {}", all_clauses.len());

        let solver = Cadical::new();
        // Set Cadical options:
        // TODO: make separate options for main/deriver solvers.
        if let Some(s) = &cli.cadical_options {
            for part in s.split(",") {
                let parts: Vec<&str> = part.splitn(2, '=').collect();
                let key = parts[0];
                let value = parts[1].parse().unwrap();
                info!("Cadical option: {}={}", key, value);
                solver.set_option(key, value);
            }
        }
        // Add all original clauses to the solver:
        for clause in all_clauses.iter() {
            solver.add_clause(clause_to_external(clause));
        }

        let pool = determine_vars_pool(&cli.path_cnf, &cli.allowed_vars, &cli.banned_vars);
        let options = Options {
            seed,
            ban_used_variables: cli.ban_used,
            ..DEFAULT_OPTIONS
        };
        let searcher = BackdoorSearcher::new(SatSolver::new_cadical(solver), pool, options);

        SearcherActor {
            tx_derived_clauses,
            rx_learned_clauses,
            cli,
            searcher,
            all_clauses,
            finish,
        }
    }

    fn run(&mut self) {
        // // Create and open the file with results:
        // let mut file_results = Some(create_line_writer("results.csv"));
        // if let Some(f) = &mut file_results {
        //     writeln!(f, "run,status,size").unwrap();
        // }

        let mut num_learnts_via_callback = 0;
        match &self.searcher.solver {
            SatSolver::Cadical(solver) => {
                solver.unsafe_set_learn(10, |clause| {
                    let mut clause = clause_from_external(clause);
                    clause.sort_by_key(|lit| lit.inner());

                    // for lit in clause.iter() {
                    //     assert!(solver.is_active(lit.to_external()));
                    // }

                    if self.all_clauses.insert(clause.clone()) {
                        // if clause.len() <= 3 {
                        //     info!("New learned clause in Deriver: {}", display_slice(&clause));
                        // }
                        num_learnts_via_callback += 1;
                    }
                });
            }
        }

        if self.cli.budget_presolve > 0 {
            info!("Pre-solving with {} conflicts budget...", self.cli.budget_presolve);
            match &self.searcher.solver {
                SatSolver::Cadical(solver) => {
                    solver.limit("conflicts", self.cli.budget_presolve as i32);
                    let time_solve = Instant::now();
                    let res = solver.solve().unwrap();
                    let time_solve = time_solve.elapsed();
                    match res {
                        SolveResponse::Interrupted => {
                            info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
                            // do nothing
                        }
                        SolveResponse::Unsat => {
                            info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
                            // return Ok(SolveResult::UNSAT);
                            return;
                        }
                        SolveResponse::Sat => {
                            info!("SAT in {:.1} s", time_solve.as_secs_f64());
                            let model = (1..=solver.vars())
                                .map(|i| {
                                    let v = Var::from_external(i as u32);
                                    match solver.val(i as i32).unwrap() {
                                        LitValue::True => Lit::new(v, false),
                                        LitValue::False => Lit::new(v, true),
                                    }
                                })
                                .collect_vec();
                            info!("Model: {}", display_slice(&model));
                            // return Ok(SolveResult::SAT(model));
                            return;
                        }
                    }
                    solver.internal_backtrack(0);
                }
            }
        }

        // Cartesian product of hard tasks:
        let mut cubes_product: Vec<Vec<Lit>> = vec![vec![]];

        // Budget for filtering:
        let mut budget_filter = self.cli.budget_filter;

        'out: loop {
            if self.finish.load(Ordering::Acquire) {
                info!("Finishing searcher.");
                break;
            }

            info!("num_learnts_via_callback = {}", num_learnts_via_callback);

            let mut num_new_learnts = 0;
            loop {
                match self.rx_learned_clauses.try_recv() {
                    Ok(Message::LearnedClause(learned_clause)) => {
                        // Note: learned_clause is already sorted
                        if self.all_clauses.insert(learned_clause.clone()) {
                            // log::info!("Received new learned clause: {}", display_slice(&learned_clause));
                            num_new_learnts += 1;
                            self.searcher.solver.add_clause(&learned_clause);
                        }
                    }
                    Ok(Message::DerivedClause(_)) => {
                        panic!("Unexpected DerivedClause message.");
                    }
                    Ok(Message::Terminate) => {
                        info!("Searcher received termination message.");
                        break 'out;
                    }
                    Err(TryRecvError::Disconnected) => {
                        info!("Channel disconnected.");
                        break 'out;
                    }
                    Err(TryRecvError::Empty) => {
                        // The queue is empty, stop receiving
                        break;
                    }
                }
            }
            info!("Received {} new learned clauses", num_new_learnts);

            // Perform backdoor search and derive clauses
            if let Some(result) = self.searcher.run(
                self.cli.backdoor_size,
                self.cli.num_iters,
                self.cli.stagnation_limit,
                self.cli.run_timeout,
                Some(((1u64 << self.cli.backdoor_size) - 1) as f64 / (1u64 << self.cli.backdoor_size) as f64),
                0,
                None,
            ) {
                let backdoor = result.best_instance.get_variables();
                let hard_tasks = get_hard_tasks(&backdoor, self.searcher.solver.as_cadical());
                debug!("Backdoor {} has {} hard tasks", display_slice(&backdoor), hard_tasks.len());
                assert_eq!(hard_tasks.len() as u64, result.best_fitness.num_hard);

                if hard_tasks.is_empty() {
                    info!("Found strong backdoor: {}", display_slice(&backdoor));
                    info!("Just solving...");
                    match &mut self.searcher.solver {
                        SatSolver::Cadical(solver) => {
                            // solver.reset_assumptions();
                            let time_solve = Instant::now();
                            let res = solver.solve().unwrap();
                            let time_solve = time_solve.elapsed();
                            match res {
                                SolveResponse::Interrupted => {
                                    info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
                                    // do nothing
                                }
                                SolveResponse::Unsat => {
                                    info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
                                    break 'out;
                                }
                                SolveResponse::Sat => {
                                    info!("SAT in {:.1} s", time_solve.as_secs_f64());
                                    let model = (1..=solver.vars())
                                        .map(|i| {
                                            let v = Var::from_external(i as u32);
                                            match solver.val(i as i32).unwrap() {
                                                LitValue::True => Lit::new(v, false),
                                                LitValue::False => Lit::new(v, true),
                                            }
                                        })
                                        .collect_vec();
                                    info!("Model: {}", display_slice(&model));
                                    break 'out;
                                }
                            }
                        }
                    }
                    unreachable!();
                }

                for &var in backdoor.iter() {
                    // assert!(self.searcher.solver.is_active(var), "var {} in backdoor is not active", var);
                    if !self.searcher.solver.is_active(var) {
                        log::error!("var {} in backdoor is not active", var);
                    }
                }

                // Derive clauses from hard tasks in the backdoor
                if !self.cli.no_derive {
                    info!("Deriving clauses from {} hard tasks in the backdoor...", hard_tasks.len());
                    let time_derive = Instant::now();
                    let derived_clauses = derive_clauses(&hard_tasks, self.cli.derive_ternary);
                    let time_derive = time_derive.elapsed();
                    info!(
                        "Derived {} clauses ({} units, {} binary, {} ternary, {} other) for backdoor in {:.1}s",
                        derived_clauses.len(),
                        derived_clauses.iter().filter(|c| c.len() == 1).count(),
                        derived_clauses.iter().filter(|c| c.len() == 2).count(),
                        derived_clauses.iter().filter(|c| c.len() == 3).count(),
                        derived_clauses.iter().filter(|c| c.len() > 3).count(),
                        time_derive.as_secs_f64()
                    );

                    // Deduplicate derived clauses
                    let mut new_derived_clauses = Vec::new();
                    for mut clause in derived_clauses {
                        clause.sort_by_key(|lit| lit.inner());
                        if self.all_clauses.insert(clause.clone()) {
                            new_derived_clauses.push(clause)
                        }
                    }

                    debug!("Adding {} new derived clauses to the solver...", new_derived_clauses.len());
                    for lemma in new_derived_clauses.iter() {
                        self.searcher.solver.add_clause(lemma);
                    }

                    // Send new derived clauses to the solver
                    info!("Sending {} new derived clauses...", new_derived_clauses.len());
                    for clause in new_derived_clauses {
                        // log::info!("Sending new derived clause: {}", display_slice(&clause));
                        self.tx_derived_clauses
                            .send(Message::DerivedClause(clause))
                            .unwrap_or_else(|e| panic!("Failed to send derived clause: {}", e));
                    }
                }

                // Remove non-active variables from all cubes:
                cubes_product = cubes_product
                    .into_iter()
                    .map(|cube| cube.into_iter().filter(|&lit| self.searcher.solver.is_active(lit.var())).collect())
                    .collect();
                let hard_tasks: Vec<Vec<Lit>> = hard_tasks
                    .into_iter()
                    .map(|cube| cube.into_iter().filter(|lit| self.searcher.solver.is_active(lit.var())).collect())
                    .collect();

                info!(
                    "Going to produce a product of size {} * {} = {}",
                    cubes_product.len(),
                    hard_tasks.len(),
                    cubes_product.len() * hard_tasks.len()
                );
                // if let Some(f) = &mut file_results {
                //     writeln!(f, "{},product,{}", run_number, cubes_product.len() * hard.len())?;
                // }
                let variables = {
                    let mut s = HashSet::new();
                    s.extend(cubes_product[0].iter().map(|lit| lit.var()));
                    s.extend(backdoor.iter().filter(|&&var| self.searcher.solver.is_active(var)));
                    s.into_iter().sorted().collect_vec()
                };
                debug!("Total {} variables: {}", variables.len(), display_slice(&variables));
                for &var in variables.iter() {
                    assert!(self.searcher.solver.is_active(var), "var {} is not active", var);
                }

                info!(
                    "Constructing trie out of {} potential cubes...",
                    cubes_product.len() * hard_tasks.len()
                );
                let time_trie_construct = Instant::now();
                let mut trie = Trie::new();
                let pb = ProgressBar::new((cubes_product.len() * hard_tasks.len()) as u64);
                pb.set_style(
                    ProgressStyle::with_template("{spinner:.green} [{elapsed}] [{bar:40.cyan/white}] {pos:>6}/{len} (ETA: {eta}) {msg}")
                        .unwrap()
                        .progress_chars("#>-"),
                );
                pb.set_message("trie construction");
                let mut num_normal_cubes: u64 = 0;
                'prod: for (old, new) in iproduct!(cubes_product, hard_tasks).progress_with(pb) {
                    let cube = concat_cubes(old, new);
                    for i in 1..cube.len() {
                        if cube[i] == -cube[i - 1] {
                            // Skip the cube with inconsistent literals:
                            // log::warn!("Skipping the concatenated cube {} with inconsistent literals", display_slice(&cube));
                            continue 'prod;
                        }
                    }
                    assert_eq!(cube.len(), variables.len());
                    assert!(zip_eq(&cube, &variables).all(|(lit, var)| lit.var() == *var));
                    if let (true, _) = trie.insert(cube.iter().map(|lit| lit.negated())) {
                        num_normal_cubes += 1;
                    }
                }
                let time_trie_construct = time_trie_construct.elapsed();
                info!(
                    "Trie of size {} with {} leaves constructed out of {} normal cubes in {:.1}s",
                    trie.len(),
                    trie.num_leaves(),
                    num_normal_cubes,
                    time_trie_construct.as_secs_f64()
                );

                info!("Filtering {} hard cubes via trie...", trie.num_leaves());
                let time_filter = Instant::now();
                let mut valid = Vec::new();
                match &mut self.searcher.solver {
                    SatSolver::Cadical(solver) => {
                        propcheck_all_trie_via_internal(solver, &variables, &trie, 0, Some(&mut valid), None);
                    }
                }
                drop(trie);
                cubes_product = valid;
                info!(
                    "Filtered down to {} cubes via trie in {:.1}s",
                    cubes_product.len(),
                    time_filter.elapsed().as_secs_f64()
                );
                // if let Some(f) = &mut file_results {
                //     writeln!(f, "{},propagate,{}", run_number, cubes_product.len())?;
                // }

                if cubes_product.is_empty() {
                    info!("No more cubes left!");
                    cubes_product = vec![vec![]];
                    continue 'out;
                }

                // TODO: handle units?

                // Derivation after trie-filtering:
                if !self.cli.no_derive {
                    info!("Deriving clauses from {} cubes...", cubes_product.len());
                    let time_derive = Instant::now();
                    let derived_clauses = derive_clauses(&cubes_product, self.cli.derive_ternary);
                    let time_derive = time_derive.elapsed();
                    info!(
                        "Derived {} clauses ({} units, {} binary, {} ternary, {} other) for {} cubes in {:.1}s",
                        derived_clauses.len(),
                        derived_clauses.iter().filter(|c| c.len() == 1).count(),
                        derived_clauses.iter().filter(|c| c.len() == 2).count(),
                        derived_clauses.iter().filter(|c| c.len() == 3).count(),
                        derived_clauses.iter().filter(|c| c.len() > 3).count(),
                        cubes_product.len(),
                        time_derive.as_secs_f64()
                    );
                    // debug!("[{}]", derived_clauses.iter().map(|c| display_slice(c)).join(", "));

                    let mut new_clauses: Vec<Vec<Lit>> = Vec::new();
                    for mut lemma in derived_clauses {
                        lemma.sort_by_key(|lit| lit.inner());
                        if self.all_clauses.insert(lemma.clone()) {
                            // if let Some(f) = &mut file_derived_clauses {
                            //     write_clause(f, &lemma)?;
                            // }
                            new_clauses.push(lemma.clone());
                            // all_derived_clauses.push(lemma);
                        }
                    }
                    info!(
                        "Derived {} new clauses ({} units, {} binary, {} ternary, {} other)",
                        new_clauses.len(),
                        new_clauses.iter().filter(|c| c.len() == 1).count(),
                        new_clauses.iter().filter(|c| c.len() == 2).count(),
                        new_clauses.iter().filter(|c| c.len() == 3).count(),
                        new_clauses.iter().filter(|c| c.len() > 2).count()
                    );
                    debug!("[{}]", new_clauses.iter().map(|c| display_slice(c)).join(", "));

                    debug!("Adding {} new derived clauses to the solver...", new_clauses.len());
                    for lemma in new_clauses.iter() {
                        self.searcher.solver.add_clause(lemma);
                    }

                    info!("Sending {} new derived clauses...", new_clauses.len());
                    for lemma in new_clauses {
                        self.tx_derived_clauses
                            .send(Message::DerivedClause(lemma))
                            .unwrap_or_else(|e| panic!("Failed to send derived clause: {}", e));
                    }

                    // debug!(
                    //     "So far derived {} new clauses ({} units, {} binary, {} ternary, {} other)",
                    //     all_derived_clauses.len(),
                    //     all_derived_clauses.iter().filter(|c| c.len() == 1).count(),
                    //     all_derived_clauses.iter().filter(|c| c.len() == 2).count(),
                    //     all_derived_clauses.iter().filter(|c| c.len() == 3).count(),
                    //     all_derived_clauses.iter().filter(|c| c.len() > 2).count()
                    // );
                }

                if cubes_product.len() > self.cli.max_product {
                    info!(
                        "Too many cubes in the product ({} > {}), restarting",
                        cubes_product.len(),
                        self.cli.max_product
                    );
                    cubes_product = vec![vec![]];
                    continue 'out;
                }
            } else {
                info!("Searcher finished without result. Resetting banned variables.");
                self.searcher.banned_vars.clear();
                continue;
            }

            // Remove non-active variables from all cubes:
            cubes_product = cubes_product
                .into_iter()
                .map(|cube| cube.into_iter().filter(|&lit| self.searcher.solver.is_active(lit.var())).collect())
                .collect();

            info!("Filtering {} hard cubes via limited solver...", cubes_product.len());
            let time_filter = Instant::now();
            let num_cubes_before_filtering = cubes_product.len();
            let num_conflicts = match &self.searcher.solver {
                SatSolver::Cadical(solver) => solver.conflicts() as u64,
            };
            info!("conflicts budget: {}", budget_filter);
            let num_conflicts_limit = num_conflicts + budget_filter;
            let mut in_budget = true;

            if self.cli.use_sorted_filtering {
                debug!("Computing neighbors...");
                let time_compute_neighbors = Instant::now();
                let mut neighbors: HashMap<(Lit, Lit), Vec<usize>> = HashMap::new();
                for (i, cube) in cubes_product.iter().enumerate() {
                    for (&a, &b) in cube.iter().tuple_combinations() {
                        neighbors.entry((a, b)).or_default().push(i);
                    }
                }
                let time_compute_neighbors = time_compute_neighbors.elapsed();
                debug!(
                    "Computed neighbors (size={}, cubes={}) in {:.1}s",
                    neighbors.len(),
                    neighbors.values().map(|vs| vs.len()).sum::<usize>(),
                    time_compute_neighbors.as_secs_f64()
                );

                let compute_cube_score = |cube: &[Lit], neighbors: &HashMap<(Lit, Lit), Vec<usize>>| {
                    let mut score: f64 = 0.0;
                    for (&a, &b) in cube.iter().tuple_combinations() {
                        if let Some(neighbors) = neighbors.get(&(a, b)) {
                            let d = neighbors.len();
                            if d != 0 {
                                score += 1.0 / d as f64;
                                if d == 1 {
                                    score += 50.0;
                                }
                            }
                        }
                    }
                    score
                };

                debug!("Computing cube score...");
                let time_cube_scores = Instant::now();
                let mut cube_score: Vec<f64> = cubes_product.iter().map(|cube| compute_cube_score(cube, &neighbors)).collect();
                let time_cube_scores = time_cube_scores.elapsed();
                debug!(
                    "Computed cube scores (size={}) in {:.1}s",
                    cube_score.len(),
                    time_cube_scores.as_secs_f64()
                );

                let mut remaining_cubes: Vec<usize> = (0..cubes_product.len()).collect();
                let mut indet_cubes: Vec<usize> = Vec::new();

                let verb = false;

                while !remaining_cubes.is_empty() {
                    let num_conflicts = match &self.searcher.solver {
                        SatSolver::Cadical(solver) => solver.conflicts() as u64,
                    };
                    if num_conflicts > num_conflicts_limit {
                        info!("Budget exhausted");
                        break;
                    }

                    if false {
                        // debug!("Asserting...");
                        let time_asserting = Instant::now();
                        for &i in remaining_cubes.iter() {
                            assert!(
                                (compute_cube_score(&cubes_product[i], &neighbors) - cube_score[i]).abs() <= 1e-6,
                                "compute = {}, score = {}",
                                compute_cube_score(&cubes_product[i], &neighbors),
                                cube_score[i]
                            );
                        }
                        let time_asserting = time_asserting.elapsed();
                        debug!("Asserted in {:.1}s", time_asserting.as_secs_f64());
                    }

                    let best_cube_position = remaining_cubes
                        .iter()
                        .position_max_by_key(|&&i| OrderedFloat(cube_score[i]))
                        .unwrap();
                    let best_cube = remaining_cubes.swap_remove(best_cube_position);
                    let best_cube_score = cube_score[best_cube];

                    if best_cube_score > 0.0 {
                        // debug!(
                        //     "Max score ({}) cube: {}",
                        //     best_cube_score,
                        //     display_slice(&cubes[best_cube])
                        // );
                        match &self.searcher.solver {
                            SatSolver::Cadical(solver) => {
                                solver.reset_assumptions();
                                for &lit in cubes_product[best_cube].iter() {
                                    solver.assume(lit.to_external()).unwrap();
                                }
                                solver.limit("conflicts", self.cli.num_conflicts as i32);
                                // debug!("Solving {}...", display_slice(&best_cube));
                                let time_solve = Instant::now();
                                let res = solver.solve().unwrap();
                                let time_solve = time_solve.elapsed();
                                match res {
                                    SolveResponse::Unsat => {
                                        if verb {
                                            debug!(
                                                "UNSAT in {:.1}s for cube with score {}: {}",
                                                time_solve.as_secs_f64(),
                                                best_cube_score,
                                                display_slice(&cubes_product[best_cube])
                                            );
                                        }
                                        let time_rescore = Instant::now();
                                        for (&a, &b) in cubes_product[best_cube].iter().tuple_combinations() {
                                            let d = neighbors[&(a, b)].len();
                                            if d == 0 {
                                                continue;
                                            } else if d == 1 {
                                                // debug!("should derive {}", display_slice(&[-a, -b]));
                                                assert_eq!(neighbors[&(a, b)][0], best_cube);
                                                cube_score[best_cube] = 0.0;
                                            } else {
                                                for &i in neighbors[&(a, b)].iter() {
                                                    cube_score[i] -= 1.0 / d as f64;
                                                    cube_score[i] += 1.0 / (d - 1) as f64;
                                                    if d - 1 == 1 {
                                                        cube_score[i] += 50.0;
                                                    }
                                                }
                                            }
                                            neighbors.get_mut(&(a, b)).unwrap().retain(|&i| i != best_cube);
                                        }
                                        let time_rescore = time_rescore.elapsed();
                                        if verb || time_rescore.as_secs_f64() > 1.0 {
                                            debug!("Rescored in {:.1}s", time_rescore.as_secs_f64());
                                        }
                                    }
                                    SolveResponse::Interrupted => {
                                        if verb {
                                            debug!(
                                                "INDET in {:.1}s for cube with score {}: {}",
                                                time_solve.as_secs_f64(),
                                                best_cube_score,
                                                display_slice(&cubes_product[best_cube])
                                            );
                                        }
                                        let time_rescore = Instant::now();
                                        for (&a, &b) in cubes_product[best_cube].iter().tuple_combinations() {
                                            let ns = neighbors.get_mut(&(a, b)).unwrap();
                                            let d = ns.len();
                                            for i in ns.drain(..) {
                                                // score[cube] -= 1 / d
                                                cube_score[i] -= 1.0 / d as f64;
                                            }
                                            assert_eq!(neighbors[&(a, b)].len(), 0);
                                        }
                                        let time_rescore = time_rescore.elapsed();
                                        if verb {
                                            debug!("Rescored in {:.1}s", time_rescore.as_secs_f64());
                                        }
                                        indet_cubes.push(best_cube);
                                    }
                                    SolveResponse::Sat => {
                                        if verb {
                                            debug!(
                                                "SAT in {:.1}s for cube with score {}: {}",
                                                time_solve.as_secs_f64(),
                                                best_cube_score,
                                                display_slice(&cubes_product[best_cube])
                                            );
                                        }
                                        // let model = (1..=solver.vars())
                                        //     .map(|i| {
                                        //         let v = Var::from_external(i as u32);
                                        //         match solver.val(i as i32).unwrap() {
                                        //             LitValue::True => Lit::new(v, false),
                                        //             LitValue::False => Lit::new(v, true),
                                        //         }
                                        //     })
                                        //     .collect_vec();
                                        // final_model = Some(model);
                                        break;
                                    }
                                }
                            }
                        }
                    } else {
                        indet_cubes.push(best_cube);
                        break;
                    }
                }

                // TODO: handle SAT
                // if let Some(model) = final_model {
                //     return Ok(SolveResult::SAT(model));
                // }

                // Populate the set of ALL clauses:
                // match &self.searcher.solver {
                //     SatSolver::Cadical(solver) => {
                //         debug!("Retrieving clauses from the solver...");
                //         let time_extract = Instant::now();
                //         let mut num_new = 0;
                //         let mut new_new = Vec::new();
                //         for clause in solver.extract_clauses(true) {
                //             if clause.len() > 10 {
                //                 continue;
                //             }
                //             let mut clause = clause_from_external(clause);
                //             clause.sort_by_key(|lit| lit.inner());
                //             for lit in clause.iter() {
                //                 assert!(self.searcher.solver.is_active(lit.var()));
                //             }
                //             if self.all_clauses.insert(clause.clone()) {
                //                 num_new += 1;
                //                 new_new.push(clause);
                //             }
                //         }
                //         let time_extract = time_extract.elapsed();
                //         // total_time_extract += time_extract;
                //         debug!("Extracted {} new clauses in {:.1}s", num_new, time_extract.as_secs_f64());
                //         debug!("[{}]", new_new.iter().map(display_slice).join(", "));
                //         // debug!(
                //         //      "So far total {} clauses, total spent {:.3}s for extraction",
                //         //      all_clauses.len(),
                //         //      total_time_extract.as_secs_f64()
                //         //  );
                //     }
                // }

                cubes_product = cubes_product
                    .into_iter()
                    .enumerate()
                    .filter_map(|(i, cube)| {
                        if remaining_cubes.contains(&i) || indet_cubes.contains(&i) {
                            Some(cube)
                        } else {
                            None
                        }
                    })
                    .collect();
            } else {
                cubes_product.shuffle(&mut self.searcher.rng);
                let pb = ProgressBar::new(cubes_product.len() as u64);
                pb.set_style(
                    ProgressStyle::with_template("{spinner:.green} [{elapsed}] [{bar:40.cyan/white}] {pos:>6}/{len} (ETA: {eta}) {msg}")
                        .unwrap()
                        .progress_chars("#>-"),
                );
                pb.set_message("filtering");
                cubes_product.retain(|cube| {
                    pb.inc(1);

                    // TODO: handle SAT
                    // if final_model.is_some() {
                    //     return false;
                    // }

                    if !in_budget {
                        return true;
                    }

                    let num_conflicts = match &self.searcher.solver {
                        SatSolver::Cadical(solver) => solver.conflicts() as u64,
                    };
                    if num_conflicts > num_conflicts_limit {
                        debug!("Budget exhausted");
                        in_budget = false;
                    }

                    if !in_budget {
                        return true;
                    }

                    match &self.searcher.solver {
                        SatSolver::Cadical(solver) => {
                            solver.reset_assumptions();
                            for &lit in cube.iter() {
                                solver.assume(lit.to_external()).unwrap();
                            }
                            solver.limit("conflicts", self.cli.num_conflicts as i32);
                            let time_solve = Instant::now();
                            let res = solver.solve().unwrap();
                            let time_solve = time_solve.elapsed();

                            match res {
                                SolveResponse::Interrupted => true,
                                SolveResponse::Unsat => false,
                                SolveResponse::Sat => {
                                    let model = (1..=solver.vars())
                                        .map(|i| {
                                            let v = Var::from_external(i as u32);
                                            match solver.val(i as i32).unwrap() {
                                                LitValue::True => Lit::new(v, false),
                                                LitValue::False => Lit::new(v, true),
                                            }
                                        })
                                        .collect_vec();
                                    info!("SAT in {:.1} s", time_solve.as_secs_f64());
                                    info!("Model: {}", display_slice(&model));
                                    // final_model = Some(model);
                                    // TODO: break out of the outer loop (currently not possible due to closure in retain)
                                    false
                                }
                            }
                        }
                    }
                });
                pb.finish_and_clear();

                // TODO: handle SAT
                // if let Some(model) = final_model {
                //     return Ok(SolveResult::SAT(model));
                // }

                // Populate the set of ALL clauses:
                // match &self.searcher.solver {
                //     SatSolver::Cadical(solver) => {
                //         debug!("Retrieving clauses from the solver...");
                //         // let time_extract = Instant::now();
                //         // let mut num_new = 0;
                //         for clause in solver.extract_clauses(true) {
                //             let mut clause = clause_from_external(clause);
                //             clause.sort_by_key(|lit| lit.inner());
                //             all_new_clauses.insert(clause);
                //             // num_new += 1;
                //         }
                //         // let time_extract = time_extract.elapsed();
                //         // total_time_extract += time_extract;
                //         // debug!("Extracted {} new clauses in {:.1}s", num_new, time_extract.as_secs_f64());
                //         // debug!(
                //         //     "So far total {} clauses, total spent {:.3}s for extraction",
                //         //     all_clauses.len(),
                //         //     total_time_extract.as_secs_f64()
                //         // );
                //     }
                // }
            }
            let time_filter = time_filter.elapsed();
            debug!(
                "Filtered {} down to {} cubes via solver in {:.1}s",
                num_cubes_before_filtering,
                cubes_product.len(),
                time_filter.as_secs_f64()
            );
            // if let Some(f) = &mut file_results {
            //     writeln!(f, "{},limited,{}", run_number, cubes_product.len())?;
            // }

            // Update the budget for filtering:
            budget_filter = (budget_filter as f64 * self.cli.factor_budget_filter) as u64;

            if cubes_product.is_empty() {
                info!("No more cubes left!");
                cubes_product = vec![vec![]];
                continue 'out;
            }

            // Derivation after filtering:
            if !self.cli.no_derive {
                info!("Deriving clauses from {} cubes...", cubes_product.len());
                let time_derive = Instant::now();
                let derived_clauses = derive_clauses(&cubes_product, self.cli.derive_ternary);
                let time_derive = time_derive.elapsed();
                info!(
                    "Derived {} clauses ({} units, {} binary, {} ternary, {} other) for {} cubes in {:.1}s",
                    derived_clauses.len(),
                    derived_clauses.iter().filter(|c| c.len() == 1).count(),
                    derived_clauses.iter().filter(|c| c.len() == 2).count(),
                    derived_clauses.iter().filter(|c| c.len() == 3).count(),
                    derived_clauses.iter().filter(|c| c.len() > 3).count(),
                    cubes_product.len(),
                    time_derive.as_secs_f64()
                );
                // debug!("[{}]", derived_clauses.iter().map(|c| display_slice(c)).join(", "));

                let mut new_clauses: Vec<Vec<Lit>> = Vec::new();
                for mut lemma in derived_clauses {
                    lemma.sort_by_key(|lit| lit.inner());
                    if self.all_clauses.insert(lemma.clone()) {
                        // if let Some(f) = &mut file_derived_clauses {
                        //     write_clause(f, &lemma)?;
                        // }
                        new_clauses.push(lemma.clone());
                        // all_derived_clauses.push(lemma);
                    }
                }
                info!(
                    "Derived {} new clauses ({} units, {} binary, {} ternary, {} other)",
                    new_clauses.len(),
                    new_clauses.iter().filter(|c| c.len() == 1).count(),
                    new_clauses.iter().filter(|c| c.len() == 2).count(),
                    new_clauses.iter().filter(|c| c.len() == 3).count(),
                    new_clauses.iter().filter(|c| c.len() > 2).count()
                );
                debug!("[{}]", new_clauses.iter().map(|c| display_slice(c)).join(", "));

                debug!("Adding {} new derived clauses to the solver...", new_clauses.len());
                for lemma in new_clauses.iter() {
                    self.searcher.solver.add_clause(lemma);
                }

                info!("Sending {} new derived clauses...", new_clauses.len());
                for lemma in new_clauses {
                    self.tx_derived_clauses
                        .send(Message::DerivedClause(lemma))
                        .unwrap_or_else(|e| panic!("Failed to send derived clause: {}", e));
                }

                // debug!(
                //     "So far derived {} new clauses ({} units, {} binary, {} ternary, {} other)",
                //     all_derived_clauses.len(),
                //     all_derived_clauses.iter().filter(|c| c.len() == 1).count(),
                //     all_derived_clauses.iter().filter(|c| c.len() == 2).count(),
                //     all_derived_clauses.iter().filter(|c| c.len() == 3).count(),
                //     all_derived_clauses.iter().filter(|c| c.len() > 2).count()
                // );
            }

            // done
        }
    }
}

// Solver Actor, which manages the main SAT solving process
struct SolverActor {
    tx_learned_clauses: Sender<Message>,
    rx_derived_clauses: Receiver<Message>,
    cli: Cli,
    solver: Cadical,
    all_clauses: HashSet<Vec<Lit>>,
}

impl SolverActor {
    fn new(tx_learned_clauses: Sender<Message>, rx_derived_clauses: Receiver<Message>, cli: Cli) -> Self {
        let mut all_clauses: HashSet<Vec<Lit>> = HashSet::new();
        for mut clause in parse_dimacs(&cli.path_cnf) {
            clause.sort_by_key(|lit| lit.inner());
            all_clauses.insert(clause);
        }
        info!("Original clauses: {}", all_clauses.len());

        let solver = Cadical::new();
        // Set Cadical options:
        if let Some(s) = &cli.cadical_options {
            for part in s.split(",") {
                let parts: Vec<&str> = part.splitn(2, '=').collect();
                let key = parts[0];
                let value = parts[1].parse().unwrap();
                info!("Cadical option: {}={}", key, value);
                solver.set_option(key, value);
            }
        }
        // Add all original clauses to the solver:
        for clause in all_clauses.iter() {
            solver.add_clause(clause_to_external(clause));
        }

        SolverActor {
            tx_learned_clauses,
            rx_derived_clauses,
            cli,
            solver,
            all_clauses,
        }
    }

    fn run(&mut self) -> SolveResult {
        let mut num_learnts_via_callback = 0;
        self.solver.unsafe_set_learn(10, |clause| {
            let mut clause = clause_from_external(clause);
            clause.sort_by_key(|lit| lit.inner());

            // for lit in clause.iter() {
            //     assert!(self.solver.is_active(lit.to_external()));
            // }

            if self.all_clauses.insert(clause.clone()) {
                // info!("New learned clause: {}", display_slice(&clause));
                self.tx_learned_clauses
                    .send(Message::LearnedClause(clause))
                    .unwrap_or_else(|e| panic!("Failed to send learned clause: {}", e));
                num_learnts_via_callback += 1;
            }
        });

        if self.cli.budget_presolve > 0 {
            info!("Pre-solving with {} conflicts budget...", self.cli.budget_presolve);
            self.solver.limit("conflicts", self.cli.budget_presolve as i32);
            let time_solve = Instant::now();
            let res = self.solver.solve().unwrap();
            let time_solve = time_solve.elapsed();
            match res {
                SolveResponse::Interrupted => {
                    info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
                    // do nothing
                }
                SolveResponse::Unsat => {
                    info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
                    return SolveResult::UNSAT;
                }
                SolveResponse::Sat => {
                    info!("SAT in {:.1} s", time_solve.as_secs_f64());
                    let model = (1..=self.solver.vars())
                        .map(|i| {
                            let v = Var::from_external(i as u32);
                            match self.solver.val(i as i32).unwrap() {
                                LitValue::True => Lit::new(v, false),
                                LitValue::False => Lit::new(v, true),
                            }
                        })
                        .collect_vec();
                    info!("Model: {}", display_slice(&model));
                    return SolveResult::SAT;
                }
            }
            self.solver.internal_backtrack(0);
        }

        loop {
            // Listen for derived clauses from searchers
            let mut num_new_derived_clauses = 0;
            while let Ok(Message::DerivedClause(derived_clause)) = self.rx_derived_clauses.try_recv() {
                // Note: we assume `derived_clause` is already sorted!
                if self.all_clauses.insert(derived_clause.clone()) {
                    // log::info!("Received new derived clause: {}", display_slice(&derived_clause));
                    num_new_derived_clauses += 1;
                    self.solver.add_clause(clause_to_external(&derived_clause));
                }
            }
            info!("Received {} new derived clauses", num_new_derived_clauses);

            info!("num_learnts_via_callback = {}", num_learnts_via_callback);

            // Set the conflict limit (budget) for this solving trial
            self.solver.limit("conflicts", self.cli.budget_solve as i32);

            // Try solving with the conflicts budget
            info!("Solving with budget {}...", self.cli.budget_solve);
            let res = self.solver.solve().unwrap();
            info!("Solving done: {:?}", res);

            // If the solver reaches UNSAT or SAT, return the result and terminate
            if matches!(res, SolveResponse::Unsat | SolveResponse::Sat) {
                info!("Solver reached a solution: {:?}", res);
                // Send termination message to all searchers
                self.tx_learned_clauses
                    .send(Message::Terminate)
                    .unwrap_or_else(|e| panic!("Failed to send termination message: {}", e));
                return if res == SolveResponse::Unsat {
                    SolveResult::UNSAT
                } else {
                    SolveResult::SAT
                };
            }

            // // Send learned clauses back to searchers
            // let mut num_new_learnts = 0;
            // for clause in self.solver.extract_clauses(true) {
            //     let mut clause = clause_from_external(clause);
            //     clause.sort_by_key(|lit| lit.inner());
            //
            //     if self.all_clauses.insert(clause.clone()) {
            //         num_new_learnts += 1;
            //         info!("Sending new learned clause: {}", display_slice(&clause));
            //         self.tx_learned_clauses
            //             .send(Message::LearnedClause(clause))
            //             .unwrap_or_else(|e| panic!("Failed to send learned clause: {}", e));
            //     }
            // }
            // info!("Sent {} new learned clauses", num_new_learnts);
        }
    }
}

// Main function to set up the actors and start the simulation
fn solve(cli: Cli) -> color_eyre::Result<SolveResult> {
    // Create channels for communication between the searcher and solver
    let (tx_derived_clauses, rx_derived_clauses) = unbounded();
    let (tx_learned_clauses, rx_learned_clauses) = unbounded();

    // Create the solver actor
    let mut solver_actor = SolverActor::new(tx_learned_clauses, rx_derived_clauses, cli.clone());

    let finish = Arc::new(AtomicBool::new(false));

    let mut parts_for_derivers: Vec<(Sender<Message>, Receiver<Message>)> = Vec::new();
    let mut parts_for_mediator: Vec<(Sender<Message>, Receiver<Message>)> = Vec::new();
    for _ in 0..cli.num_derivers {
        let (txd, rxd) = unbounded();
        let (txl, rxl) = unbounded();
        parts_for_derivers.push((txd, rxl));
        parts_for_mediator.push((txl, rxd));
    }
    let mediator = {
        let (txs_learned_clauses, rxs_derived_clauses): (Vec<_>, Vec<_>) = parts_for_mediator.into_iter().unzip();
        let finish = Arc::clone(&finish);
        thread::spawn(move || {
            thread_priority::set_current_thread_priority(thread_priority::ThreadPriority::Min).unwrap();
            let mut rxs = Vec::new();
            // Note: 0-th receiver must be the learned clauses from the solver!
            rxs.push(rx_learned_clauses);
            for rx in rxs_derived_clauses {
                rxs.push(rx);
            }

            let mut sel = Select::new();
            for r in rxs.iter() {
                sel.recv(r);
            }

            loop {
                if finish.load(Ordering::Acquire) {
                    info!("Finishing searcher.");
                    break;
                }

                let index = sel.ready();
                match rxs[index].try_recv() {
                    Ok(msg) => {
                        if index == 0 {
                            for tx in txs_learned_clauses.iter() {
                                tx.send(msg.clone()).unwrap();
                            }
                        } else {
                            tx_derived_clauses.send(msg).unwrap();
                        }
                    }
                    Err(TryRecvError::Empty) => {
                        continue;
                    }
                    Err(TryRecvError::Disconnected) => {
                        break;
                    }
                }
            }
        })
    };

    let derivers: Vec<_> = parts_for_derivers
        .into_iter()
        .enumerate()
        .map(|(i, (tx, rx))| {
            let cli = cli.clone();
            let finish = Arc::clone(&finish);
            thread::spawn(move || {
                thread_priority::set_current_thread_priority(thread_priority::ThreadPriority::Min).unwrap();
                let seed = cli.seed + i as u64;
                let mut searcher_actor = SearcherActor::new(tx, rx, cli, finish, seed);
                searcher_actor.run();
            })
        })
        .collect();

    // core_affinity::set_for_current(core_affinity::CoreId { id: 0 });

    // Run the solver actor in the main thread
    let result = solver_actor.run();

    // Send termination message to the searcher
    info!("Storing `true` in finish flag.");
    finish.store(true, Ordering::Release);

    // Wait for the searcher to finish (after termination message is sent)
    if false {
        for t in derivers {
            t.join().unwrap();
        }
        mediator.join().unwrap();
    }

    Ok(result) // Return the result from the solver actor
}

fn main() -> color_eyre::Result<()> {
    // Install color_eyre for better error reporting
    color_eyre::install()?;

    // Parse command-line arguments using `clap`
    let cli = Cli::parse();

    // Initialize logging
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("debug,backdoor::derivation=info")).init();
    let start_time = Instant::now();

    // Run the solver
    match solve(cli)? {
        SolveResult::UNSAT => {
            info!("UNSAT in {:.3} seconds", start_time.elapsed().as_secs_f64());
            println!("s UNSATISFIABLE");
            process::exit(20);
        }
        SolveResult::SAT => {
            info!("SAT in {:.3} seconds", start_time.elapsed().as_secs_f64());
            println!("s SATISFIABLE");
            // let mut line = String::from("v");
            // for &lit in model.iter() {
            //     if line.len() + format!(" {}", lit).len() > 100 {
            //         println!("{}", line);
            //         line = String::from("v");
            //     }
            //     line.push_str(&format!(" {}", lit));
            // }
            // line.push_str(" 0");
            // println!("{}", line);
            process::exit(10);
        }
        SolveResult::UNKNOWN => {
            info!("UNKNOWN in {:.3} seconds", start_time.elapsed().as_secs_f64());
            println!("s UNKNOWN");
        }
    }

    Ok(())
}
