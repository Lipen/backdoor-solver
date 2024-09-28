use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Condvar};
use std::time::Instant;
use std::{process, thread};

use backdoor::derivation::derive_clauses;
use backdoor::lit::Lit;
use backdoor::searcher::{BackdoorSearcher, Options, DEFAULT_OPTIONS};
use backdoor::solvers::SatSolver;
use backdoor::utils::*;
use backdoor::var::Var;

use cadical::statik::Cadical;
use cadical::SolveResponse;

use clap::Parser;

#[derive(Parser, Debug)]
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

    /// Derive ternary clauses.
    #[arg(long)]
    derive_ternary: bool,

    /// Number of conflicts (budget per task in filtering).
    #[arg(long, value_name = "INT", default_value_t = 1000)]
    num_conflicts: usize,

    /// Initial conflicts budget for solving.
    #[arg(long, value_name = "INT", default_value_t = 10000)]
    budget_solve: u64,

    /// Multiplicative factor for solving budget.
    #[arg(long, value_name = "FLOAT", default_value_t = 1.0)]
    factor_budget_solve: f64,

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
enum SolveResult {
    SAT, // TODO: model
    UNSAT,
    UNKNOWN,
}

// Messages for communication between actors
enum Message {
    DerivedClause(Vec<Lit>),
    LearnedClause(Vec<Lit>),
    Terminate,
}

// Actor responsible for the searcher
struct SearcherActor {
    tx_derived_clauses: Sender<Message>,
    rx_learned_clauses: Receiver<Message>,
    searcher: BackdoorSearcher,
    all_clauses: HashSet<Vec<Lit>>,
    finish: Arc<AtomicBool>,
}

impl SearcherActor {
    fn new(tx_derived_clauses: Sender<Message>, rx_learned_clauses: Receiver<Message>, cli: &Cli, finish: Arc<AtomicBool>) -> Self {
        let aux_solver = Cadical::new(); // This solver is for propagation only
        for clause in parse_dimacs(&cli.path_cnf) {
            aux_solver.add_clause(clause_to_external(&clause));
        }

        let pool = determine_vars_pool(&cli.path_cnf, &cli.allowed_vars, &cli.banned_vars);
        let options = Options {
            seed: cli.seed,
            ban_used_variables: false,
            ..DEFAULT_OPTIONS
        };
        let searcher = BackdoorSearcher::new(SatSolver::new_cadical(aux_solver), pool, options);
        let mut all_clauses = HashSet::new();
        for clause in parse_dimacs(&cli.path_cnf) {
            all_clauses.insert(clause);
        }

        SearcherActor {
            tx_derived_clauses,
            rx_learned_clauses,
            searcher,
            all_clauses,
            finish,
        }
    }

    fn run(&mut self, cli: &Cli) {
        loop {
            if self.finish.load(Ordering::Acquire) {
                log::info!("Finishing searcher.");
                break;
            }

            // Perform backdoor search and derive clauses
            if let Some(result) = self.searcher.run(
                cli.backdoor_size,
                cli.num_iters,
                None, // No stagnation limit
                cli.run_timeout,
                None,
                0,
                None,
            ) {
                let backdoor = result.best_instance.get_variables();
                let hard_tasks = get_hard_tasks(&backdoor, self.searcher.solver.as_cadical());

                // Derive clauses for hard tasks
                let derived_clauses = derive_clauses(&hard_tasks, cli.derive_ternary);

                // Deduplicate derived clauses and send to solver
                for mut clause in derived_clauses {
                    clause.sort_by_key(|lit| lit.inner());
                    if self.all_clauses.insert(clause.clone()) {
                        self.tx_derived_clauses
                            .send(Message::DerivedClause(clause))
                            .expect("Failed to send derived clause");
                    }
                }
            }

            // Check if any learned clauses have arrived from the solver
            while let Ok(Message::LearnedClause(learned_clause)) = self.rx_learned_clauses.try_recv() {
                if self.all_clauses.insert(learned_clause.clone()) {
                    self.searcher.solver.add_clause(&learned_clause);
                }
            }

            // Stop searcher if Terminate message is received
            if let Ok(Message::Terminate) = self.rx_learned_clauses.try_recv() {
                log::info!("Searcher received termination message.");
                break;
            }
        }
    }
}

// Solver Actor, which manages the main SAT solving process
struct SolverActor {
    solver: Cadical,
    tx_learned_clauses: Sender<Message>,
    rx_derived_clauses: Receiver<Message>,
    conflict_budget: u64,
}

impl SolverActor {
    fn new(tx_learned_clauses: Sender<Message>, rx_derived_clauses: Receiver<Message>, cli: &Cli) -> Self {
        let mut solver = Cadical::new(); // This is the main solver
        for clause in parse_dimacs(&cli.path_cnf) {
            solver.add_clause(clause_to_external(&clause));
        }

        SolverActor {
            solver,
            tx_learned_clauses,
            rx_derived_clauses,
            conflict_budget: cli.budget_solve,
        }
    }

    fn run(&mut self) -> SolveResult {
        loop {
            // Listen for derived clauses from searchers
            while let Ok(Message::DerivedClause(derived_clause)) = self.rx_derived_clauses.try_recv() {
                log::info!("Received derived clause: {}", display_slice(&derived_clause));
                self.solver.add_clause(clause_to_external(&derived_clause));
            }

            // Set the conflict limit (budget) for this solving trial
            self.solver.limit("conflicts", self.conflict_budget as i32);

            // Try solving with the current budget
            log::info!("Solving with budget {}...", self.conflict_budget);
            let res = self.solver.solve().unwrap();
            log::info!("Solving done: {:?}", res);

            // Send learned clauses back to searchers
            for learned_clause in self.solver.all_clauses_iter() {
                let mut clause = clause_from_external(learned_clause);
                clause.sort_by_key(|lit| lit.inner());
                log::info!("Learned clause: {}", display_slice(&clause));

                self.tx_learned_clauses
                    .send(Message::LearnedClause(clause))
                    .expect("Failed to send learned clause");
            }

            // If the solver reaches UNSAT or SAT, return the result and terminate
            if matches!(res, SolveResponse::Unsat | SolveResponse::Sat) {
                log::info!("Solver reached a solution: {:?}", res);
                // Send termination message to all searchers
                self.tx_learned_clauses
                    .send(Message::Terminate)
                    .expect("Failed to send termination message");
                return if res == SolveResponse::Unsat {
                    SolveResult::UNSAT
                } else {
                    SolveResult::SAT
                };
            }
        }
    }
}

// Main function to set up the actors and start the simulation
fn solve(cli: Cli) -> color_eyre::Result<SolveResult> {
    // Create channels for communication between the searcher and solver
    let (tx_derived_clauses, rx_derived_clauses) = mpsc::channel();
    let (tx_learned_clauses, rx_learned_clauses) = mpsc::channel();

    // Create the solver actor
    let mut solver_actor = SolverActor::new(tx_learned_clauses.clone(), rx_derived_clauses, &cli);

    let finish = Arc::new(AtomicBool::new(false));

    // Spawn a searcher actor in its own thread
    let searcher_thread = {
        let finish = Arc::clone(&finish);
        thread::spawn(move || {
            let mut searcher_actor = SearcherActor::new(tx_derived_clauses, rx_learned_clauses, &cli, finish);
            searcher_actor.run(&cli);
        })
    };

    // Run the solver actor in the main thread
    let result = solver_actor.run();

    // Send termination message to the searcher
    log::info!("Storing `true` in finish flag.");
    finish.store(true, Ordering::Release);

    // Wait for the searcher to finish (after termination message is sent)
    searcher_thread.join().unwrap();

    Ok(result) // Return the result from the solver actor
}

fn main() -> color_eyre::Result<()> {
    // Install color_eyre for better error reporting
    color_eyre::install()?;

    // Parse command-line arguments using `clap`
    let cli = Cli::parse();

    // Initialize logging
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();
    let start_time = Instant::now();

    // Run the solver
    match solve(cli)? {
        SolveResult::UNSAT => {
            log::info!("UNSAT in {:.3} seconds", start_time.elapsed().as_secs_f64());
            println!("s UNSATISFIABLE");
            process::exit(20);
        }
        SolveResult::SAT => {
            log::info!("SAT in {:.3} seconds", start_time.elapsed().as_secs_f64());
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
            log::info!("UNKNOWN in {:.3} seconds", start_time.elapsed().as_secs_f64());
            println!("s UNKNOWN");
        }
    }

    Ok(())
}
