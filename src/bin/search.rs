use std::collections::HashSet;
use std::io::Write;
use std::path::PathBuf;
use std::time::Instant;

use clap::Parser;
use itertools::Itertools;
use log::{debug, info};

use cadical::statik::Cadical;
use cadical::{FixedResponse, SolveResponse};

use backdoor::derivation::derive_clauses;
use backdoor::lit::Lit;
use backdoor::searcher::{BackdoorSearcher, Options, DEFAULT_OPTIONS};
use backdoor::solvers::SatSolver;
use backdoor::utils::*;
use backdoor::var::Var;

// Run this example:
// cargo run --release --bin search -- data/mult/lec_CvK_12.cnf --backdoor-size 10 --num-iters 1000

#[derive(Parser, Debug)]
#[command(author, version)]
struct Cli {
    /// Input file with CNF in DIMACS format.
    #[arg(value_name = "CNF")]
    path_cnf: PathBuf,

    /// Backdoor size.
    #[arg(long, value_name = "INT")]
    backdoor_size: usize,

    /// Number of EA iterations.
    #[arg(long, value_name = "INT")]
    num_iters: usize,

    /// Number of EA runs.
    #[arg(long, value_name = "INT", default_value_t = 1)]
    num_runs: usize,

    /// Timeout for each EA run.
    #[arg(long, value_name = "FLOAT")]
    run_timeout: Option<f64>,

    /// Path to a output file with backdoors.
    #[arg(short = 'o', long = "output", value_name = "FILE")]
    path_output: Option<PathBuf>,

    /// Random seed.
    #[arg(long, value_name = "INT", default_value_t = DEFAULT_OPTIONS.seed)]
    seed: u64,

    /// Comma-separated list of allowed variables (1-based indices).
    #[arg(long = "allow", value_name = "INT...")]
    allowed_vars: Option<String>,

    /// Comma-separated list of banned variables (1-based indices).
    #[arg(long = "ban", value_name = "INT...")]
    banned_vars: Option<String>,

    /// Do ban variables used in best backdoors on previous runs?
    #[arg(long)]
    ban_used: bool,

    /// Number of stagnated iterations before re-initialization.
    #[arg(long, value_name = "INT")]
    stagnation_limit: Option<usize>,

    /// Maximum required rho value (break EA upon reaching).
    #[arg(long, value_name = "FLOAT", default_value_t = 1.0)]
    max_rho: f64,

    /// Minimum number of EA iterations.
    #[arg(long, value_name = "INT", default_value_t = 0)]
    min_iter: usize,

    /// Path to an output file with records.
    #[arg(long = "records", value_name = "FILE")]
    path_records: Option<PathBuf>,

    /// Do derive clauses from backdoors?
    #[arg(long)]
    derive: bool,

    /// Do dump derived clauses after each EA run?
    #[arg(long)]
    dump_derived: bool,

    /// Do probe the backdoor variables?
    #[arg(long)]
    probe: bool,

    /// Do try to probe-derive all units and binary clauses?
    #[arg(long)]
    probe_derive: bool,

    /// Freeze variables.
    #[arg(long)]
    freeze: bool,

    /// Derive ternary clauses.
    #[arg(long)]
    derive_ternary: bool,

    /// Danya's propcheck-based heuristic.
    #[arg(long, value_name = "INT")]
    pool_limit: Option<usize>,

    /// Budget (in conflicts) for pre-solve.
    #[arg(long, value_name = "INT", default_value_t = 0)]
    budget_presolve: u64,

    /// Do perform checking?
    #[arg(long)]
    check: bool,
}

fn print_stats(solver: &Cadical, prefix: &str) {
    debug!("{}vars: {}", prefix, solver.vars());
    // debug!("{}active: {}", prefix, solver.active());
    debug!(
        "{}active: {}",
        prefix,
        (1..=solver.vars() as i32).filter(|&v| solver.is_active(v)).count()
    );
    debug!(
        "{}fixed: {}",
        prefix,
        (1..=solver.vars() as i32)
            .filter(|&v| match solver.fixed(v).unwrap() {
                FixedResponse::Positive | FixedResponse::Negative => true,
                FixedResponse::Unclear => false,
            })
            .count()
    );
    let solver_clauses = solver.extract_clauses(false);
    debug!("{}clauses: {}", prefix, solver_clauses.len());
    debug!("{}units: {}", prefix, solver_clauses.iter().filter(|c| c.len() == 1).count());
    debug!("{}binary: {}", prefix, solver_clauses.iter().filter(|c| c.len() == 2).count());
    debug!("{}ternary: {}", prefix, solver_clauses.iter().filter(|c| c.len() == 3).count());
    debug!("{}large: {}", prefix, solver_clauses.iter().filter(|c| c.len() > 3).count());
    let solver_all_clauses = solver.extract_clauses(true);
    debug!("{}all_clauses: {}", prefix, solver_all_clauses.len());
    debug!(
        "{}all_units: {}",
        prefix,
        solver_all_clauses.iter().filter(|c| c.len() == 1).count()
    );
    debug!(
        "{}all_binary: {}",
        prefix,
        solver_all_clauses.iter().filter(|c| c.len() == 2).count()
    );
    debug!(
        "{}all_ternary: {}",
        prefix,
        solver_all_clauses.iter().filter(|c| c.len() == 3).count()
    );
    debug!("{}all_large: {}", prefix, solver_all_clauses.iter().filter(|c| c.len() > 3).count());
    debug!("{}conflicts: {}", prefix, solver.conflicts());
    debug!("{}decisions: {}", prefix, solver.decisions());
    debug!("{}restarts: {}", prefix, solver.restarts());
    debug!("{}propagations: {}", prefix, solver.propagations());
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("debug,simple_sat::solver=info,backdoor::derivation=info"))
        .init();

    let start_time = Instant::now();
    let args = Cli::parse();
    info!("args = {:?}", args);

    // Initialize SAT solver:
    let solver = Cadical::new();
    for clause in parse_dimacs(&args.path_cnf) {
        solver.add_clause(clause.into_iter().map(|lit| lit.to_external()));
    }
    if args.freeze {
        info!("Freezing variables...");
        for i in 0..solver.vars() {
            let lit = (i + 1) as i32;
            solver.freeze(lit).unwrap();
        }
    }

    debug!("Initial Solver statistics:");
    print_stats(&solver, "  initial ");

    solver.limit("conflicts", 0);
    solver.solve()?;

    debug!("Solver statistics:");
    print_stats(&solver, "  ");

    // Create the pool of variables available for EA:
    let pool: Vec<Var> = determine_vars_pool(&args.path_cnf, &args.allowed_vars, &args.banned_vars);

    // Set up the evolutionary algorithm:
    let options = Options {
        seed: args.seed,
        ban_used_variables: args.ban_used,
        ..DEFAULT_OPTIONS
    };
    let mut searcher = BackdoorSearcher::new(SatSolver::new_cadical(solver), pool, options);

    // Create and open the file with resulting backdoors:
    let mut file_backdoors = args.path_output.as_ref().map(create_line_writer);

    // Create and open the file with records:
    let mut file_records = if let Some(path) = &args.path_records {
        let mut writer = csv::Writer::from_path(path)?;
        writer.write_record(["run", "iteration", "instance", "fitness", "num_hard", "rho", "time"])?;
        Some(writer)
    } else {
        None
    };

    // Create and open the file with derived clauses:
    let mut file_derived_clauses = if args.dump_derived {
        Some(create_line_writer("derived_clauses.txt"))
    } else {
        None
    };

    // Set of ALL clauses (original + derived):
    let mut all_clauses: HashSet<Vec<Lit>> = HashSet::new();
    for mut clause in parse_dimacs(&args.path_cnf) {
        clause.sort_by_key(|lit| lit.inner());
        all_clauses.insert(clause);
    }

    // All derived clauses:
    let mut all_derived_clauses: Vec<Vec<Lit>> = Vec::new();

    let mut _sat = false;
    let mut _unsat = false;

    if args.budget_presolve > 0 {
        info!("Pre-solving with {} conflicts budget...", args.budget_presolve);
        match &searcher.solver {
            SatSolver::Cadical(solver) => {
                solver.limit("conflicts", args.budget_presolve as i32);
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
                        _unsat = true;
                    }
                    SolveResponse::Sat => {
                        info!("SAT in {:.1} s", time_solve.as_secs_f64());
                        _sat = true;
                    }
                }
                solver.internal_backtrack(0);

                debug!("Solver statistics after pre-solve:");
                print_stats(solver, "  after pre-solve ");
            }
        }
    }

    // Probe all variables:
    if args.probe {
        info!("Probing all variables...");
        let time_failed = Instant::now();
        let mut failed = Vec::new();
        for i in 1..searcher.solver.num_vars() {
            let var = Var::from_external(i as u32);
            if !searcher.solver.is_active(var) {
                continue;
            }
            let pos_lit = Lit::new(var, false);
            let (res, _) = match &searcher.solver {
                SatSolver::Cadical(solver) => solver.propcheck(&[pos_lit.to_external()], false, false, false),
            };
            if !res {
                info!("failed literal {}", pos_lit);
                searcher.solver.add_clause(&[-pos_lit]);
                failed.push(pos_lit);
            } else {
                let neg_lit = Lit::new(var, true);
                let (res, _) = match &searcher.solver {
                    SatSolver::Cadical(solver) => solver.propcheck(&[neg_lit.to_external()], false, false, false),
                };
                if !res {
                    info!("failed literal {}", neg_lit);
                    searcher.solver.add_clause(&[-neg_lit]);
                    failed.push(neg_lit);
                } else {
                    // neither positive nor negative literal is failed
                    // info!("neither {} nor {} is failed", pos_lit, neg_lit);
                }
            }
        }
        let time_failed = time_failed.elapsed();
        debug!("Found {} failed literals in {:.3}s", failed.len(), time_failed.as_secs_f64());
        for &lit in failed.iter() {
            if !searcher.solver.is_active(lit.var()) {
                debug!("failed literal {} is not active anymore", lit);
            }
        }
    }

    for run_number in 1..=args.num_runs {
        if _sat || _unsat {
            break;
        }

        info!("Run {} / {}", run_number, args.num_runs);
        let time_run = Instant::now();

        // Run the evolutionary algorithm:
        let result = searcher
            .run(
                args.backdoor_size,
                args.num_iters,
                args.stagnation_limit,
                args.run_timeout,
                Some(args.max_rho),
                args.min_iter,
                args.pool_limit,
            )
            .unwrap();

        // Write the best found backdoor to the output file:
        if let Some(f) = &mut file_backdoors {
            writeln!(
                f,
                "Backdoor {} of size {} on iter {} with fitness = {}, rho = {}, hard = {} in {:.3} ms",
                result.best_instance,
                result.best_instance.len(),
                result.best_iteration,
                result.best_fitness.value,
                result.best_fitness.rho,
                result.best_fitness.num_hard,
                result.time.as_secs_f64() * 1000.0
            )?;
        }

        // Write the run records:
        if let Some(f) = &mut file_records {
            for record in result.records {
                f.serialize((
                    run_number,
                    record.iteration,
                    record.instance.get_variables().iter().map(|v| v.to_external()).join(","),
                    record.fitness.value,
                    record.fitness.num_hard,
                    record.fitness.rho,
                    record.time.as_secs_f64(),
                ))?;
            }
        }

        if result.best_fitness.num_hard == 0 {
            info!("Found strong backdoor: {}", result.best_instance);
            break;
        }

        let backdoor = result.best_instance.get_variables();
        let hard = get_hard_tasks(&backdoor, searcher.solver.as_cadical());
        debug!("Backdoor {} has {} hard tasks", display_slice(&backdoor), hard.len());
        assert_eq!(hard.len() as u64, result.best_fitness.num_hard);

        // Probe the backdoor variables:
        if args.probe {
            info!("Probing the backdoor variables...");
            let time_failed = Instant::now();
            let mut failed = Vec::new();
            match &searcher.solver {
                SatSolver::Cadical(solver) => {
                    for &var in backdoor.iter() {
                        let pos_lit = Lit::new(var, false);
                        let (res, _) = solver.propcheck(&[pos_lit.to_external()], false, false, false);
                        if !res {
                            info!("failed literal {}", pos_lit);
                            failed.push(pos_lit);
                        } else {
                            let neg_lit = Lit::new(var, true);
                            let (res, _) = solver.propcheck(&[neg_lit.to_external()], false, false, false);
                            if !res {
                                info!("failed literal {}", neg_lit);
                                failed.push(neg_lit);
                            } else {
                                // neither positive nor negative literal is failed
                                info!("neither {} nor {} is failed", pos_lit, neg_lit);
                            }
                        }
                    }
                }
            }
            let time_failed = time_failed.elapsed();
            debug!(
                "Found {}/{} failed literals in {:.3}s",
                failed.len(),
                backdoor.len(),
                time_failed.as_secs_f64()
            );

            info!("Probing the pairs of backdoor variables...");
            let time_failed_pairs = Instant::now();
            let mut failed_pairs = Vec::new();
            match &searcher.solver {
                SatSolver::Cadical(solver) => {
                    for (&a, &b) in backdoor
                        .iter()
                        .filter(|&&var| !(failed.contains(&Lit::new(var, false)) || failed.contains(&Lit::new(var, true))))
                        .tuple_combinations()
                    {
                        for a in [Lit::new(a, false), Lit::new(a, true)].iter() {
                            for b in [Lit::new(b, false), Lit::new(b, true)].iter() {
                                let cube = vec![a.to_external(), b.to_external()];
                                let (res, _) = solver.propcheck(&cube, false, false, true);
                                if !res {
                                    let core = solver.propcheck_get_core();
                                    info!("failed cube {} with core = {}", display_slice(&cube), display_slice(&core));
                                    failed_pairs.push(cube);
                                }
                            }
                        }
                    }
                }
            }
            let time_failed_pairs = time_failed_pairs.elapsed();
            debug!(
                "Found {} failed pairs of literals in {:.3}s",
                failed_pairs.len(),
                time_failed_pairs.as_secs_f64()
            );
        }

        if args.check {
            match &searcher.solver {
                SatSolver::Cadical(solver) => {
                    let vars_external: Vec<i32> = backdoor.iter().map(|var| var.to_external() as i32).collect();
                    for &v in vars_external.iter() {
                        assert!(solver.is_active(v), "var {} is not active", v);
                    }
                    let mut hard = Vec::new();
                    let mut easy = Vec::new();
                    let res = solver.propcheck_all_tree_via_internal(&vars_external, 0, Some(&mut hard), Some(&mut easy));
                    assert_eq!(hard.len(), res as usize);
                    let easy: Vec<Vec<Lit>> = easy
                        .into_iter()
                        .map(|cube| cube.into_iter().map(|i| Lit::from_external(i)).collect())
                        .collect();
                    debug!("Easy tasks: {}", easy.len());

                    let mut easy_cores: Vec<Vec<Lit>> = Vec::new();
                    for (i, cube) in easy.iter().enumerate() {
                        let cube_external = lits_to_external(cube);
                        let (res, _) = solver.propcheck(&cube_external, false, false, true);
                        if res {
                            panic!("Unexpected SAT on cube = {}", display_slice(&cube));
                        } else {
                            let mut core = solver.propcheck_get_core().into_iter().map(|i| Lit::from_external(i)).collect_vec();
                            assert!(!core.is_empty());
                            core.sort_by_key(|lit| lit.inner());
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

                            if false {
                                let lemma = core.iter().map(|&lit| -lit).collect_vec();
                                let lits = &lemma;

                                solver.internal_backtrack(0);

                                let res = solver.internal_propagate();
                                assert!(res);

                                let lits = lits_to_external(lits);
                                if lits.len() >= 2 {
                                    for lit in lits {
                                        assert!(solver.is_active(lit), "lit {} is not active", lit);
                                        solver.add_derived(lit);
                                    }
                                    solver.add_derived(0);
                                } else {
                                    let lit = lits[0];
                                    if solver.is_active(lit) {
                                        solver.add_unit_clause(lit);
                                        assert!(!solver.is_active(lit));
                                    } else {
                                        log::warn!("unit {} is not active", lit);
                                    }
                                }

                                let res = solver.internal_propagate();
                                assert!(res);
                            }

                            easy_cores.push(core);
                        }
                    }

                    let easy_cores: HashSet<Vec<Lit>> = easy_cores.into_iter().collect();
                    debug!("Unique easy cores: {}", easy_cores.len());
                    for (i, core) in easy_cores.iter().enumerate() {
                        debug!("[{}/{}]: {}", i + 1, easy_cores.len(), display_slice(core));

                        let lemma = core.iter().map(|&lit| -lit).collect_vec();
                        solver.add_derived_clause(lits_to_external(&lemma));
                    }

                    let hard: Vec<Vec<Lit>> = hard
                        .into_iter()
                        .map(|cube| cube.into_iter().map(|i| Lit::from_external(i)).collect())
                        .collect();
                    debug!("Hard tasks: {}", hard.len());
                    for (i, cube) in hard.iter().enumerate() {
                        debug!("[{}/{}]: {}", i + 1, hard.len(), display_slice(cube));
                    }

                    let time_derive = Instant::now();
                    let derived_clauses = derive_clauses(&hard, args.derive_ternary);
                    let time_derive = time_derive.elapsed();
                    info!(
                        "Derived {} clauses ({} units, {} binary, {} other) for backdoor in {:.1}s",
                        derived_clauses.len(),
                        derived_clauses.iter().filter(|c| c.len() == 1).count(),
                        derived_clauses.iter().filter(|c| c.len() == 2).count(),
                        derived_clauses.iter().filter(|c| c.len() > 2).count(),
                        time_derive.as_secs_f64()
                    );
                    debug!("[{}]", derived_clauses.iter().map(|c| display_slice(c)).join(", "));

                    info!("Checking (probing) derived clauses...");
                    for clause in derived_clauses.iter() {
                        let cube = clause.iter().map(|lit| -lit.to_external()).collect_vec();
                        let (res, _) = solver.propcheck(&cube, false, false, true);
                        if res {
                            info!("clause {} is not RUP", display_slice(clause));
                        } else {
                            info!("clause {} has RUP", display_slice(clause));
                        }
                    }
                }
            }
        }

        // Derive clauses from the best backdoor:
        if args.derive {
            // TODO: handle the case when `hard.len() == 1`

            let time_derive = Instant::now();
            let derived_clauses = derive_clauses(&hard, args.derive_ternary);
            let time_derive = time_derive.elapsed();
            info!(
                "Derived {} clauses ({} units, {} binary, {} other) for backdoor in {:.1}s",
                derived_clauses.len(),
                derived_clauses.iter().filter(|c| c.len() == 1).count(),
                derived_clauses.iter().filter(|c| c.len() == 2).count(),
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
                    searcher.solver.add_clause(&lemma);
                    new_clauses.push(lemma.clone());
                    all_derived_clauses.push(lemma);
                }
            }
            match &mut searcher.solver {
                SatSolver::Cadical(solver) => {
                    solver.limit("conflicts", 0);
                    solver.solve()?;
                }
            }
            debug!(
                "Derived {} new clauses ({} units, {} binary, {} other)",
                new_clauses.len(),
                new_clauses.iter().filter(|c| c.len() == 1).count(),
                new_clauses.iter().filter(|c| c.len() == 2).count(),
                new_clauses.iter().filter(|c| c.len() > 2).count()
            );
            // debug!("[{}]", new_clauses.iter().map(|c| display_slice(c)).join(", "));

            let time_run = time_run.elapsed();
            info!("Done run {} / {} in {:.1}s", run_number, args.num_runs, time_run.as_secs_f64());
            info!(
                "So far derived {} new clauses ({} units, {} binary, {} other)",
                all_derived_clauses.len(),
                all_derived_clauses.iter().filter(|c| c.len() == 1).count(),
                all_derived_clauses.iter().filter(|c| c.len() == 2).count(),
                all_derived_clauses.iter().filter(|c| c.len() > 2).count()
            );
        }
    }

    if args.derive {
        info!(
            "Total derived {} new clauses ({} units, {} binary, {} other)",
            all_derived_clauses.len(),
            all_derived_clauses.iter().filter(|c| c.len() == 1).count(),
            all_derived_clauses.iter().filter(|c| c.len() == 2).count(),
            all_derived_clauses.iter().filter(|c| c.len() > 2).count()
        );
    }

    match &searcher.solver {
        SatSolver::Cadical(solver) => {
            debug!("Final solver statistics:");
            print_stats(&solver, "  final ");
        }
    }

    println!("\nAll done in {:.3} s", start_time.elapsed().as_secs_f64());
    Ok(())
}
