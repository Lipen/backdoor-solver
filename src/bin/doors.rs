use std::collections::HashSet;
use std::fmt::Write as _;
use std::fs::File;
use std::io::LineWriter;
use std::io::Write as _;
use std::path::PathBuf;
use std::time::Instant;

use clap::Parser;
use color_eyre::eyre::bail;
use indicatif::{ProgressBar, ProgressIterator, ProgressStyle};
use itertools::{iproduct, zip_eq, Itertools};
use log::{debug, info};
use rayon::prelude::*;
use rayon::ThreadPoolBuilder;

use cadical::statik::Cadical;
use cadical::{LitValue, SolveResponse};

use backdoor::derivation::derive_clauses;
use backdoor::lit::Lit;
use backdoor::searcher::{BackdoorSearcher, Options, DEFAULT_OPTIONS};
use backdoor::solvers::SatSolver;
use backdoor::trie::Trie;
use backdoor::utils::*;
use backdoor::var::Var;

// Run this example:
// cargo run --release --bin doors -- data/mult/lec_CvK_12.cnf --backdoor-size 10 --num-iters 10000 --budget-presolve 10000 --budget-subsolve 10000 -t 4

#[derive(Parser, Debug)]
#[command(author, version)]
struct Cli {
    /// Input file with CNF in DIMACS format.
    #[arg(value_name = "CNF")]
    path_cnf: PathBuf,

    /// Path to a file with results.
    #[arg(long = "results", value_name = "FILE")]
    path_results: Option<PathBuf>,

    /// Random seed.
    #[arg(long, value_name = "INT", default_value_t = DEFAULT_OPTIONS.seed)]
    seed: u64,

    /// Backdoor size.
    #[arg(long, value_name = "INT")]
    backdoor_size: usize,

    /// Number of EA iterations.
    #[arg(long, value_name = "INT")]
    num_iters: usize,

    /// Number of stagnated iterations before re-initialization.
    #[arg(long, value_name = "INT")]
    stagnation_limit: Option<usize>,

    /// Timeout for each EA run.
    #[arg(long, value_name = "FLOAT")]
    run_timeout: Option<f64>,

    /// Do ban variables used in the best backdoors on previous runs?
    #[arg(long)]
    ban_used: bool,

    /// Reset banned used variables on empty product.
    #[arg(long)]
    reset_used_vars: bool,

    /// Comma-separated list of allowed variables (1-based indices).
    #[arg(long = "allow", value_name = "INT...")]
    allowed_vars: Option<String>,

    /// Comma-separated list of banned variables (1-based indices).
    #[arg(long = "ban", value_name = "INT...")]
    banned_vars: Option<String>,

    /// Freeze variables.
    #[arg(long)]
    freeze: bool,

    /// Do not derive clauses.
    #[arg(long)]
    no_derive: bool,

    /// Derive ternary clauses.
    #[arg(long)]
    derive_ternary: bool,

    /// Number of threads for filtering.
    #[arg(short, long, value_name = "INT", default_value_t = 1)]
    threads: usize,

    /// Budget (in conflicts) for pre-solve.
    #[arg(long, value_name = "INT", default_value_t = 0)]
    budget_presolve: u64,

    /// Budget (in conflicts) for sub-solving hard tasks.
    #[arg(long, value_name = "INT")]
    budget_subsolve: u64,

    /// Budget (in conflicts) for inter-solving when filtering stagnates.
    #[arg(long, value_name = "INT", default_value_t = 10000)]
    budget_intersolve: u64,

    /// Budget (in conflicts) for solving phase.
    #[arg(long, value_name = "INT", default_value_t = 0)]
    budget_solve: u64,

    /// Do compute cores for easy tasks and invalid cubes.
    #[arg(long)]
    compute_cores: bool,

    /// Do add lemmas from cores.
    #[arg(long)]
    add_cores: bool,

    /// Maximum core size to be added (0 = unlimited).
    #[arg(long, default_value_t = 0)]
    max_core_size: usize,

    /// Comma-separated list of Cadical options ('key=value' pairs, e.g. 'elim=0,ilb=0,check=1').
    #[arg(long)]
    cadical_options: Option<String>,

    /// Do not print solver stats in the end.
    #[arg(long)]
    no_stats: bool,
}

#[allow(unused)]
enum SolveResult {
    SAT(Vec<Lit>),
    UNSAT,
    UNKNOWN,
}

fn solve(args: Cli) -> color_eyre::Result<SolveResult> {
    // Initialize Cadical:
    let solver = Cadical::new();

    // Set Cadical options:
    if let Some(s) = &args.cadical_options {
        for (key, value) in parse_key_value_pairs(s) {
            let value = value.parse::<i32>()?;
            info!("set option: {}={}", key, value);
            solver.set_option(key, value);
        }
    }

    // Load CNF:
    for clause in parse_dimacs(&args.path_cnf) {
        solver.add_clause(lits_to_external(&clause));
    }

    // Freeze all variables, if needed:
    if args.freeze {
        info!("Freezing variables...");
        for var in 1..=solver.vars() as i32 {
            solver.freeze(var)?;
        }
    }

    debug!("solver.vars() = {}", solver.vars());
    debug!("solver.active() = {}", solver.active());
    debug!("solver.redundant() = {}", solver.redundant());
    debug!("solver.irredundant() = {}", solver.irredundant());
    debug!("solver.clauses() = {}", solver.extract_clauses(false).len());
    debug!("solver.all_clauses() = {}", solver.extract_clauses(true).len());

    // Create the pool of variables available for EA:
    let pool: Vec<Var> = determine_vars_pool(&args.path_cnf, &args.allowed_vars, &args.banned_vars);

    // Set up the evolutionary algorithm:
    let options = Options {
        seed: args.seed,
        ban_used_variables: args.ban_used,
        ..DEFAULT_OPTIONS
    };
    let mut searcher = BackdoorSearcher::new(SatSolver::new_cadical(solver), pool, options);

    // Create and open the file with derived clauses:
    // let mut file_derived_clauses = Some(create_line_writer("derived_clauses.txt"));
    let mut file_derived_clauses: Option<LineWriter<File>> = None;

    // Create and open the file with results:
    let mut file_results = args.path_results.as_ref().map(create_line_writer);
    if let Some(f) = &mut file_results {
        writeln!(f, "run,status,size")?;
    }

    // Set of ALL clauses:
    let mut all_clauses: HashSet<Vec<Lit>> = HashSet::new();
    for mut clause in parse_dimacs(&args.path_cnf) {
        clause.sort_by_key(|lit| lit.inner());
        all_clauses.insert(clause);
    }

    // let mut final_model: Option<Vec<Lit>> = None;

    if args.budget_presolve > 0 {
        info!("Pre-solving with {} conflicts budget...", args.budget_presolve);
        match &searcher.solver {
            SatSolver::Cadical(solver) => {
                solver.limit("conflicts", args.budget_presolve as i32);
                let time_solve = Instant::now();
                let res = solver.solve()?;
                let time_solve = time_solve.elapsed();
                match res {
                    SolveResponse::Interrupted => {
                        info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
                        // do nothing
                    }
                    SolveResponse::Unsat => {
                        info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
                        return Ok(SolveResult::UNSAT);
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
                        return Ok(SolveResult::SAT(model));
                    }
                }
                solver.internal_backtrack(0);
            }
        }
    }

    // Cartesian product of hard tasks:
    let mut cubes_product: Vec<Vec<Lit>> = vec![vec![]];

    // All derived clauses:
    let mut all_derived_clauses: Vec<Vec<Lit>> = Vec::new();

    let pool = ThreadPoolBuilder::new().num_threads(args.threads).build()?;

    let mut run_number = 0;
    loop {
        run_number += 1;
        info!("Run {}", run_number);
        let time_run = Instant::now();

        // Remove non-active variables from all cubes:
        cubes_product = cubes_product
            .into_iter()
            .map(|cube| cube.into_iter().filter(|&lit| searcher.solver.is_active(lit.var())).collect())
            .collect();

        // Reset banned used variables:
        if args.reset_used_vars && cubes_product == vec![vec![]] {
            searcher.banned_vars.clear();
        }

        if let Some(result) = searcher.run(
            args.backdoor_size,
            args.num_iters,
            args.stagnation_limit,
            args.run_timeout,
            Some(((1u64 << args.backdoor_size) - 1) as f64 / (1u64 << args.backdoor_size) as f64),
            0,
            None,
        ) {
            let backdoor = result.best_instance.get_variables();
            let hard = get_hard_tasks(&backdoor, searcher.solver.as_cadical());
            debug!("Backdoor {} has {} hard tasks", display_slice(&backdoor), hard.len());
            assert_eq!(hard.len() as u64, result.best_fitness.num_hard);

            if hard.len() == 0 {
                info!("Found strong backdoor: {}", display_slice(&backdoor));

                info!("Just solving...");
                match &mut searcher.solver {
                    SatSolver::Cadical(solver) => {
                        solver.reset_assumptions();
                        let time_solve = Instant::now();
                        let res = solver.solve()?;
                        let time_solve = time_solve.elapsed();
                        match res {
                            SolveResponse::Interrupted => {
                                info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
                                // do nothing
                            }
                            SolveResponse::Unsat => {
                                info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
                                return Ok(SolveResult::UNSAT);
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
                                return Ok(SolveResult::SAT(model));
                            }
                        }
                    }
                }

                unreachable!();
            }

            // // Populate the set of ALL clauses:
            // match &mut searcher.solver {
            //     SatSolver::Cadical(solver) => {
            //         debug!("Retrieving clauses from the solver...");
            //         let time_extract = Instant::now();
            //         let mut num_new = 0;
            //         for clause in solver.extract_clauses(true) {
            //             let mut clause = lits_from_external(clause);
            //             clause.sort_by_key(|lit| lit.inner());
            //             all_clauses.insert(clause);
            //             num_new += 1;
            //         }
            //         let time_extract = time_extract.elapsed();
            //         total_time_extract += time_extract;
            //         debug!("Extracted {} new clauses in {:.1}s", num_new, time_extract.as_secs_f64());
            //         debug!(
            //             "So far total {} clauses, total spent {:.3}s for extraction",
            //             all_clauses.len(),
            //             total_time_extract.as_secs_f64()
            //         );
            //     }
            // };

            if args.compute_cores {
                match &searcher.solver {
                    SatSolver::Cadical(solver) => {
                        let vars_external: Vec<i32> = backdoor
                            .iter()
                            .map(|var| var.to_external() as i32)
                            .filter(|&v| solver.is_active(v))
                            .collect();
                        debug!("Using vars for cores: {}", display_slice(&vars_external));
                        // for &v in vars_external.iter() {
                        //     assert!(solver.is_active(v), "var {} in backdoor is not active", v);
                        // }
                        // let orig_hard_len = hard.len();
                        let mut hard = Vec::new();
                        let mut easy = Vec::new();
                        let res = solver.propcheck_all_tree_via_internal(&vars_external, 0, Some(&mut hard), Some(&mut easy));
                        assert_eq!(hard.len(), res as usize);
                        // assert_eq!(hard.len(), orig_hard_len);
                        let easy: Vec<Vec<Lit>> = easy
                            .into_iter()
                            .map(|cube| cube.into_iter().map(|i| Lit::from_external(i)).collect())
                            .collect();
                        debug!("Easy tasks: {}", easy.len());

                        let mut easy_cores: HashSet<Vec<Lit>> = HashSet::new();
                        for (i, cube) in easy.iter().enumerate() {
                            let (res, _) = solver.propcheck(&cube.iter().map(|lit| lit.to_external()).collect_vec(), false, false, true);
                            assert!(!res, "Unexpected SAT on cube = {}", display_slice(&cube));
                            let core = solver
                                .propcheck_get_core()
                                .into_iter()
                                .map(|i| Lit::from_external(i))
                                .rev()
                                .collect_vec();
                            assert!(!core.is_empty());
                            debug!(
                                "{}/{}: core = {} for cube = {}",
                                i + 1,
                                easy.len(),
                                display_slice(&core),
                                display_slice(cube)
                            );
                            assert_eq!(
                                core.last().unwrap(),
                                cube.last().unwrap(),
                                "core.last() = {}, cube.last() = {}",
                                core.last().unwrap(),
                                cube.last().unwrap()
                            );
                            easy_cores.insert(core);
                        }
                        debug!("Unique cores from easy tasks: {}", easy_cores.len());
                        debug!("[{}]", easy_cores.iter().map(|c| display_slice(c)).join(", "));

                        if args.add_cores {
                            debug!("Adding {} cores...", easy_cores.len());
                            let mut num_added = 0;
                            for core in easy_cores.iter() {
                                // Skip big cores:
                                if args.max_core_size > 0 && core.len() > args.max_core_size {
                                    continue;
                                }

                                let mut lemma = core.iter().map(|&lit| -lit).collect_vec();
                                lemma.sort_by_key(|lit| lit.inner());
                                if all_clauses.insert(lemma.clone()) {
                                    if let Some(f) = &mut file_derived_clauses {
                                        write_clause(f, &lemma)?;
                                    }
                                    searcher.solver.add_clause(&lemma);
                                    all_derived_clauses.push(lemma);
                                    num_added += 1;
                                }
                            }
                            debug!("Added {} new lemmas from cores", num_added);
                        }
                    }
                }

                match &searcher.solver {
                    SatSolver::Cadical(solver) => {
                        let res = solver.internal_propagate();
                        assert!(res);
                    }
                }
            }

            // Check that all variables in the backdoor are active:
            for &var in backdoor.iter() {
                // assert!(searcher.solver.is_active(var), "var {} in backdoor is not active", var);
                if !searcher.solver.is_active(var) {
                    log::error!("var {} in backdoor is not active", var);
                }
            }

            if hard.len() == 1 {
                info!("Adding {} units to the solver: {}", hard[0].len(), display_slice(&hard[0]));
                for &lit in &hard[0] {
                    if all_clauses.insert(vec![lit]) {
                        if let Some(f) = &mut file_derived_clauses {
                            write_clause(f, &[lit])?;
                        }
                        searcher.solver.add_clause(&[lit]);
                        all_derived_clauses.push(vec![lit]);
                    }
                }
                cubes_product = vec![vec![]];
                continue;
            }

            // ------------------------------------------------------------------------

            // Derivation for backdoor:
            if !args.no_derive {
                info!("Deriving clauses for {} hard tasks...", hard.len());
                let time_derive = Instant::now();
                let derived_clauses = derive_clauses(&hard, args.derive_ternary);
                let time_derive = time_derive.elapsed();
                info!(
                    "Derived {} clauses ({} units, {} binary, {} ternary, {} other) for backdoor in {:.1}s",
                    derived_clauses.len(),
                    derived_clauses.iter().filter(|c| c.len() == 1).count(),
                    derived_clauses.iter().filter(|c| c.len() == 2).count(),
                    derived_clauses.iter().filter(|c| c.len() == 3).count(),
                    derived_clauses.iter().filter(|c| c.len() > 2).count(),
                    time_derive.as_secs_f64()
                );
                // debug!("[{}]", derived_clauses.iter().map(|c| display_slice(c)).join(", "));

                let mut new_clauses = Vec::new();
                for mut lemma in derived_clauses {
                    lemma.sort_by_key(|lit| lit.inner());
                    if all_clauses.insert(lemma.clone()) {
                        if let Some(f) = &mut file_derived_clauses {
                            write_clause(f, &lemma)?;
                        }
                        new_clauses.push(lemma.clone());
                        all_derived_clauses.push(lemma);
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
                for lemma in new_clauses {
                    searcher.solver.add_clause(&lemma);
                }
            }

            // Remove non-active variables from all cubes:
            cubes_product = cubes_product
                .into_iter()
                .map(|cube| cube.into_iter().filter(|&lit| searcher.solver.is_active(lit.var())).collect())
                .collect();

            let hard: Vec<Vec<Lit>> = hard
                .into_iter()
                .map(|cube| cube.into_iter().filter(|lit| searcher.solver.is_active(lit.var())).collect())
                .collect();

            // ------------------------------------------------------------------------

            info!(
                "Going to produce a product of size {} * {} = {}",
                cubes_product.len(),
                hard.len(),
                cubes_product.len() * hard.len()
            );
            if let Some(f) = &mut file_results {
                writeln!(f, "{},product,{}", run_number, cubes_product.len() * hard.len())?;
            }
            let variables = {
                let mut s = HashSet::new();
                s.extend(cubes_product[0].iter().map(|lit| lit.var()));
                s.extend(backdoor.iter().filter(|&&var| searcher.solver.is_active(var)));
                s.into_iter().sorted().collect_vec()
            };
            debug!("Total {} variables: {}", variables.len(), display_slice(&variables));
            for &var in variables.iter() {
                assert!(searcher.solver.is_active(var), "var {} is not active", var);
            }

            info!("Constructing trie out of {} potential cubes...", cubes_product.len() * hard.len());
            let time_trie_construct = Instant::now();
            let mut trie = Trie::new();
            let pb = ProgressBar::new((cubes_product.len() * hard.len()) as u64);
            pb.set_style(
                ProgressStyle::with_template("{spinner:.green} [{elapsed}] [{bar:40.cyan/white}] {pos:>6}/{len} (ETA: {eta}) {msg}")?
                    .progress_chars("#>-"),
            );
            pb.set_message("trie construction");
            let mut num_normal_cubes: u64 = 0;
            'out: for (old, new) in iproduct!(cubes_product, hard).progress_with(pb) {
                let cube = concat_cubes(old, new);
                for i in 1..cube.len() {
                    if cube[i] == -cube[i - 1] {
                        // Skip the cube with inconsistent literals:
                        // log::warn!("Skipping the concatenated cube {} with inconsistent literals", display_slice(&cube));
                        continue 'out;
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
            let mut invalid = Vec::new(); // TODO: remove 'invalid' extraction
            match &mut searcher.solver {
                SatSolver::Cadical(solver) => {
                    propcheck_all_trie_via_internal(
                        solver,
                        &variables,
                        &trie,
                        0,
                        Some(&mut valid),
                        if args.compute_cores { Some(&mut invalid) } else { None },
                    );
                }
            }
            drop(trie);
            cubes_product = valid;
            info!(
                "Filtered down to {} cubes via trie in {:.1}s",
                cubes_product.len(),
                time_filter.elapsed().as_secs_f64()
            );
            if let Some(f) = &mut file_results {
                writeln!(f, "{},propagate,{}", run_number, cubes_product.len())?;
            }

            if args.compute_cores {
                match &searcher.solver {
                    SatSolver::Cadical(solver) => {
                        debug!("Invalid sub-cubes: {}", invalid.len());
                        let mut invalid_cores: HashSet<Vec<Lit>> = HashSet::new();
                        for (i, cube) in invalid.iter().enumerate() {
                            let (res, _) = solver.propcheck(&cube.iter().map(|lit| lit.to_external()).collect_vec(), false, false, true);
                            assert!(!res, "Unexpected SAT on cube = {}", display_slice(&cube));
                            let core = solver
                                .propcheck_get_core()
                                .into_iter()
                                .map(|i| Lit::from_external(i))
                                .rev()
                                .collect_vec();
                            assert!(!core.is_empty());
                            debug!(
                                "{}/{}: core = {} for cube = {}",
                                i + 1,
                                invalid.len(),
                                display_slice(&core),
                                display_slice(cube)
                            );
                            assert_eq!(
                                core.last().unwrap(),
                                cube.last().unwrap(),
                                "core.last() = {}, cube.last() = {}",
                                core.last().unwrap(),
                                cube.last().unwrap()
                            );
                            invalid_cores.insert(core);
                        }
                        debug!("Unique cores from invalid cubes: {}", invalid_cores.len());
                        debug!("[{}]", invalid_cores.iter().map(|c| display_slice(c)).join(", "));

                        if args.add_cores {
                            debug!("Adding {} cores...", invalid_cores.len());
                            let mut num_added = 0;
                            for core in invalid_cores.iter() {
                                // Skip big cores:
                                if args.max_core_size > 0 && core.len() > args.max_core_size {
                                    continue;
                                }

                                let mut lemma = core.iter().map(|&lit| -lit).collect_vec();
                                lemma.sort_by_key(|lit| lit.inner());
                                if all_clauses.insert(lemma.clone()) {
                                    if let Some(f) = &mut file_derived_clauses {
                                        write_clause(f, &lemma)?;
                                    }
                                    searcher.solver.add_clause(&lemma);
                                    all_derived_clauses.push(lemma);
                                    num_added += 1;
                                }
                            }
                            debug!("Added {} new lemmas from cores", num_added);
                        }
                    }
                }
            }

            if cubes_product.is_empty() {
                info!("No more cubes to solve after {} runs", run_number);
                return Ok(SolveResult::UNSAT);

                // info!("Just solving...");
                // match &mut searcher.solver {
                //     SatSolver::Cadical(solver) => {
                //         solver.reset_assumptions();
                //         let time_solve = Instant::now();
                //         let res = solver.solve()?;
                //         let time_solve = time_solve.elapsed();
                //         match res {
                //             SolveResponse::Interrupted => {
                //                 info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
                //                 // do nothing
                //             }
                //             SolveResponse::Unsat => {
                //                 info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
                //                 return Ok(SolveResult::UNSAT);
                //             }
                //             SolveResponse::Sat => {
                //                 info!("SAT in {:.1} s", time_solve.as_secs_f64());
                //                 let model = (1..=solver.vars())
                //                     .map(|i| {
                //                         let v = Var::from_external(i as u32);
                //                         match solver.val(i as i32).unwrap() {
                //                             LitValue::True => Lit::new(v, false),
                //                             LitValue::False => Lit::new(v, true),
                //                         }
                //                     })
                //                     .collect_vec();
                //                 return Ok(SolveResult::SAT(model));
                //             }
                //         }
                //         solver.internal_backtrack(0);
                //     }
                // }
                //
                // unreachable!()
            } else if cubes_product.len() == 1 {
                debug!("Adding {} units to the solver", cubes_product[0].len());
                for &lit in &cubes_product[0] {
                    if all_clauses.insert(vec![lit]) {
                        if let Some(f) = &mut file_derived_clauses {
                            write_clause(f, &[lit])?;
                        }
                        searcher.solver.add_clause(&[lit]);
                        all_derived_clauses.push(vec![lit]);
                    }
                }
                cubes_product = vec![vec![]];
                continue;
            }

            // Derivation after trie-filtering:
            if !args.no_derive {
                info!("Deriving clauses for {} cubes...", cubes_product.len());
                let time_derive = Instant::now();
                let derived_clauses = derive_clauses(&cubes_product, args.derive_ternary);
                let time_derive = time_derive.elapsed();
                info!(
                    "Derived {} clauses ({} units, {} binary, {} ternary, {} other) for {} cubes in {:.1}s",
                    derived_clauses.len(),
                    derived_clauses.iter().filter(|c| c.len() == 1).count(),
                    derived_clauses.iter().filter(|c| c.len() == 2).count(),
                    derived_clauses.iter().filter(|c| c.len() == 3).count(),
                    derived_clauses.iter().filter(|c| c.len() > 2).count(),
                    cubes_product.len(),
                    time_derive.as_secs_f64()
                );
                // debug!("[{}]", derived_clauses.iter().map(|c| display_slice(c)).join(", "));

                let mut new_clauses: Vec<Vec<Lit>> = Vec::new();
                for mut lemma in derived_clauses {
                    lemma.sort_by_key(|lit| lit.inner());
                    if all_clauses.insert(lemma.clone()) {
                        if let Some(f) = &mut file_derived_clauses {
                            write_clause(f, &lemma)?;
                        }
                        new_clauses.push(lemma.clone());
                        all_derived_clauses.push(lemma);
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
                for lemma in new_clauses {
                    searcher.solver.add_clause(&lemma);
                }

                debug!(
                    "So far derived {} new clauses ({} units, {} binary, {} ternary, {} other)",
                    all_derived_clauses.len(),
                    all_derived_clauses.iter().filter(|c| c.len() == 1).count(),
                    all_derived_clauses.iter().filter(|c| c.len() == 2).count(),
                    all_derived_clauses.iter().filter(|c| c.len() == 3).count(),
                    all_derived_clauses.iter().filter(|c| c.len() > 2).count()
                );
            }

            // if cubes_product.len() > args.max_product {
            //     info!(
            //         "Too many cubes in the product ({} > {}), restarting",
            //         cubes_product.len(),
            //         args.max_product
            //     );
            //     cubes_product = vec![vec![]];
            //     continue;
            // }
        } else {
            if args.reset_used_vars {
                searcher.banned_vars.clear();
            }
        }

        // Remove non-active variables from all cubes:
        cubes_product = cubes_product
            .into_iter()
            .map(|cube| cube.into_iter().filter(|&lit| searcher.solver.is_active(lit.var())).collect())
            .collect();

        info!("Filtering {} hard cubes via limited solver...", cubes_product.len());
        let time_filter = Instant::now();
        let num_cubes_before_filtering = cubes_product.len();

        let cubes_product_par = cubes_product.into_par_iter();
        cubes_product = vec![];
        pool.install(|| {
            let pb = ProgressBar::new(num_cubes_before_filtering as u64);
            cubes_product = cubes_product_par
                .filter(|cube| {
                    pb.inc(1);
                    // let time_solve = Instant::now();

                    let solver = Cadical::new();
                    // for clause in all_clauses.iter() {
                    //     solver.add_clause(lits_to_external(clause));
                    // }
                    for clause in parse_dimacs(&args.path_cnf) {
                        solver.add_clause(lits_to_external(&clause));
                    }
                    for clause in all_derived_clauses.iter() {
                        solver.add_clause(lits_to_external(clause));
                    }
                    for &lit in cube.iter() {
                        solver.add_clause([lit.to_external()]);
                    }

                    // let new = Cadical::new();
                    // solver.copy_to(&new);
                    // let solver = new;

                    solver.limit("conflicts", args.budget_subsolve as i32);
                    let res = solver.solve().unwrap();
                    // let time_solve = time_solve.elapsed();
                    // pb.println(format!(
                    //     "{} -> {:?} after {} conflicts in {:.3}s",
                    //     display_slice(&cube),
                    //     res,
                    //     solver.conflicts(),
                    //     time_solve.as_secs_f64()
                    // ));
                    match res {
                        SolveResponse::Sat => {
                            // TODO: handle SAT
                            panic!("Unexpected SAT");
                        }
                        SolveResponse::Unsat => false,
                        SolveResponse::Interrupted => true,
                    }
                })
                // .progress_with(pb)
                .collect();
        });

        let time_filter = time_filter.elapsed();
        debug!(
            "Filtered {} down to {} cubes via solver in {:.1}s",
            num_cubes_before_filtering,
            cubes_product.len(),
            time_filter.as_secs_f64()
        );
        if let Some(f) = &mut file_results {
            writeln!(f, "{},limited,{}", run_number, cubes_product.len())?;
        }

        if cubes_product.is_empty() {
            info!("No more cubes to solve after {} runs", run_number);
            return Ok(SolveResult::UNSAT);

            // info!("Just solving...");
            // match &mut searcher.solver {
            //     SatSolver::Cadical(solver) => {
            //         solver.reset_assumptions();
            //         let time_solve = Instant::now();
            //         let res = solver.solve()?;
            //         let time_solve = time_solve.elapsed();
            //         match res {
            //             SolveResponse::Interrupted => {
            //                 info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
            //                 // do nothing
            //             }
            //             SolveResponse::Unsat => {
            //                 info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
            //                 return Ok(SolveResult::UNSAT);
            //             }
            //             SolveResponse::Sat => {
            //                 info!("SAT in {:.1} s", time_solve.as_secs_f64());
            //                 let model = (1..=solver.vars())
            //                     .map(|i| {
            //                         let v = Var::from_external(i as u32);
            //                         match solver.val(i as i32).unwrap() {
            //                             LitValue::True => Lit::new(v, false),
            //                             LitValue::False => Lit::new(v, true),
            //                         }
            //                     })
            //                     .collect_vec();
            //                 return Ok(SolveResult::SAT(model));
            //             }
            //         }
            //         solver.internal_backtrack(0);
            //     }
            // }
            //
            // unreachable!()
        } else if cubes_product.len() == 1 {
            info!("Adding {} units to the solver", cubes_product[0].len());
            for &lit in &cubes_product[0] {
                if all_clauses.insert(vec![lit]) {
                    if let Some(f) = &mut file_derived_clauses {
                        write_clause(f, &[lit])?;
                    }
                    searcher.solver.add_clause(&[lit]);
                    all_derived_clauses.push(vec![lit]);
                }
            }
            cubes_product = vec![vec![]];
            continue;
        }

        // Derivation after filtering:
        if !args.no_derive {
            info!("Deriving clauses for {} cubes...", cubes_product.len());
            let time_derive = Instant::now();
            let derived_clauses = derive_clauses(&cubes_product, args.derive_ternary);
            let time_derive = time_derive.elapsed();
            info!(
                "Derived {} clauses ({} units, {} binary, {} ternary, {} other) for {} cubes in {:.1}s",
                derived_clauses.len(),
                derived_clauses.iter().filter(|c| c.len() == 1).count(),
                derived_clauses.iter().filter(|c| c.len() == 2).count(),
                derived_clauses.iter().filter(|c| c.len() == 3).count(),
                derived_clauses.iter().filter(|c| c.len() > 2).count(),
                cubes_product.len(),
                time_derive.as_secs_f64()
            );
            // debug!("[{}]", derived_clauses.iter().map(|c| display_slice(c)).join(", "));

            let mut new_clauses: Vec<Vec<Lit>> = Vec::new();
            for mut lemma in derived_clauses {
                lemma.sort_by_key(|lit| lit.inner());
                if all_clauses.insert(lemma.clone()) {
                    if let Some(f) = &mut file_derived_clauses {
                        write_clause(f, &lemma)?;
                    }
                    new_clauses.push(lemma.clone());
                    all_derived_clauses.push(lemma);
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
            for lemma in new_clauses {
                searcher.solver.add_clause(&lemma);
            }

            debug!(
                "So far derived {} new clauses ({} units, {} binary, {} ternary, {} other)",
                all_derived_clauses.len(),
                all_derived_clauses.iter().filter(|c| c.len() == 1).count(),
                all_derived_clauses.iter().filter(|c| c.len() == 2).count(),
                all_derived_clauses.iter().filter(|c| c.len() == 3).count(),
                all_derived_clauses.iter().filter(|c| c.len() > 2).count()
            );
        };

        if cubes_product.len() == num_cubes_before_filtering {
            // No change, solve a little bit in the main thread...
            info!("Filtering stagnated!");

            info!("Just solving for {} conflicts...", args.budget_intersolve);
            match &mut searcher.solver {
                SatSolver::Cadical(solver) => {
                    solver.limit("conflicts", args.budget_intersolve as i32);
                    let time_solve = Instant::now();
                    let res = solver.solve()?;
                    let time_solve = time_solve.elapsed();
                    match res {
                        SolveResponse::Interrupted => {
                            info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
                            // do nothing
                        }
                        SolveResponse::Unsat => {
                            info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
                            return Ok(SolveResult::UNSAT);
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
                            return Ok(SolveResult::SAT(model));
                        }
                    }
                }
            }
        }

        if args.budget_solve > 0 {
            info!("Just solving with {} conflicts budget...", args.budget_solve);
            match &mut searcher.solver {
                SatSolver::Cadical(solver) => {
                    solver.reset_assumptions();
                    solver.limit("conflicts", args.budget_solve as i32);
                    let time_solve = Instant::now();
                    let res = solver.solve()?;
                    let time_solve = time_solve.elapsed();
                    match res {
                        SolveResponse::Interrupted => {
                            info!("UNKNOWN in {:.1} s", time_solve.as_secs_f64());
                            // do nothing
                        }
                        SolveResponse::Unsat => {
                            info!("UNSAT in {:.1} s", time_solve.as_secs_f64());
                            return Ok(SolveResult::UNSAT);
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
                            return Ok(SolveResult::SAT(model));
                        }
                    }
                    solver.internal_backtrack(0);
                }
            }
        }

        // Populate the set of ALL clauses:
        match &mut searcher.solver {
            SatSolver::Cadical(solver) => {
                debug!("Retrieving clauses from the solver...");
                let time_extract = Instant::now();
                let mut num_new = 0;
                for clause in solver.extract_clauses(true) {
                    let mut clause = lits_from_external(clause);
                    clause.sort_by_key(|lit| lit.inner());
                    if all_clauses.insert(clause) {
                        num_new += 1;
                    }
                }
                let time_extract = time_extract.elapsed();
                debug!("Extracted {} new clauses in {:.1}s", num_new, time_extract.as_secs_f64());
            }
        };

        let time_run = time_run.elapsed();
        info!("Done run {} in {:.1}s", run_number, time_run.as_secs_f64());
    }
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("debug,backdoor::derivation=info")).init();

    let start_time = Instant::now();
    let args = Cli::parse();
    info!("args = {:?}", args);

    if args.add_cores && !args.compute_cores {
        bail!("Cannot add cores (`--add-cores` flag) without computing them (`--compute-cores` flag)");
    }

    match solve(args)? {
        SolveResult::UNSAT => {
            info!("UNSAT in {:.3} s", start_time.elapsed().as_secs_f64());
            println!("s UNSATISFIABLE");
            std::process::exit(20);
        }
        SolveResult::SAT(model) => {
            info!("SAT in {:.3} s", start_time.elapsed().as_secs_f64());
            println!("s SATISFIABLE");
            let mut line = "v".to_string();
            for &lit in model.iter() {
                if line.len() + format!(" {}", lit).len() > 100 {
                    println!("{}", line);
                    line = "v".to_string();
                }
                write!(line, " {}", lit)?;
            }
            write!(line, " 0")?;
            println!("{}", line);
            std::process::exit(10);
        }
        SolveResult::UNKNOWN => {
            info!("INDET in {:.3} s", start_time.elapsed().as_secs_f64());
            println!("s UNKNOWN");
        }
    }

    Ok(())
}
