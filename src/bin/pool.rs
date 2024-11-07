use std::path::PathBuf;
use std::time::Instant;

use clap::Parser;
use indicatif::{ProgressBar, ProgressIterator};
use itertools::zip_eq;
use log::info;

use cadical::statik::Cadical;

use backdoor::lit::Lit;
use backdoor::pool::{new_solver_pool, CubeTask};
use backdoor::utils::*;
use backdoor::var::Var;

// Run this example:
// cargo run --release --bin pool -- data/lec_mult_CvK_6x6.cnf --num-vars 12 -t 4

#[derive(Parser, Debug)]
#[command(author, version)]
struct Cli {
    /// Input file with CNF in DIMACS format.
    #[arg(value_name = "CNF")]
    path_cnf: PathBuf,

    /// Number of threads.
    #[arg(short = 't', long, value_name = "INT")]
    num_threads: usize,

    /// Number of variables.
    #[arg(long, value_name = "INT")]
    num_vars: usize,
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("debug,simple_sat::solver=info,backdoor::derivation=info"))
        .init();

    let start_time = Instant::now();
    let args = Cli::parse();
    info!("args = {:?}", args);

    let clauses: Vec<Vec<Lit>> = parse_dimacs(&args.path_cnf).collect();
    let pool = new_solver_pool::<CubeTask, _, _>(
        args.num_threads,
        move |_| {
            let solver = Cadical::new();
            for clause in clauses.iter() {
                solver.add_clause(lits_to_external(clause));
            }
            solver
        },
        |task, solver| task.solve_with(solver),
    );
    let variables: Vec<Var> = (1..=args.num_vars).map(|i| Var::from_external(i as u32)).collect();
    let mut num_tasks: usize = 0;
    for (i, cube) in product_repeat([true, false].into_iter(), variables.len()).enumerate() {
        let cube: Vec<Lit> = zip_eq(&variables, cube).map(|(&v, s)| Lit::new(v, s)).collect();
        num_tasks += 1;
        pool.submit(CubeTask::new(i, cube));
    }
    info!("Submitted {} tasks", num_tasks);

    // info!("Results so far:");
    // let mut num_results = 0;
    // for (task, res, time) in pool.results() {
    //     // info!("{:?} in {:.1}s for cube = {}", res, time.as_secs_f64(), display_slice(&task.cube));
    //     num_results += 1;
    // }
    // info!("Got {} results", num_results);
    // pool.finish().for_each(drop);

    info!("Joining...");
    let pb = ProgressBar::new(num_tasks as u64);
    let results: Vec<_> = pool.join().take(num_tasks).progress_with(pb).collect();
    info!("Got {} results", results.len());
    // let mut results = results;
    // results.sort_by_key(|r| r.0.i);
    // for (task, res, time) in results.iter() {
    //     info!("{:?} in {:.3}ms for cube = {}", res, time.as_secs_f64(), display_slice(&task.cube));
    // }
    info!(
        "Total CPU time: {:.1}s",
        results.iter().map(|(_, _, time)| time.as_secs_f64()).sum::<f64>()
    );

    info!("Finishing...");
    let num_left = pool.finish().count();
    info!("Leftover tasks: {}", num_left);

    println!("\nAll done in {:.3} s", start_time.elapsed().as_secs_f64());
    Ok(())
}
