use std::fmt::Debug;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use log::{debug, trace};

use cadical::statik::Cadical;
use cadical::SolveResponse;
use sat_nexus_utils::pool::Pool;

use crate::lit::Lit;

#[derive(Debug)]
pub struct CubeTask {
    pub i: usize,
    pub cube: Vec<Lit>,
}

impl CubeTask {
    pub fn new(i: usize, cube: Vec<Lit>) -> Self {
        Self { i, cube }
    }
}

impl CubeTask {
    pub fn solve_with(&self, solver: &Cadical) -> SolveResponse {
        for &lit in self.cube.iter() {
            solver.assume(lit.to_external()).unwrap();
        }
        // solver.limit("conflicts", 1000);
        let res = solver.solve().unwrap();
        // if res == SolveResponse::Unsat {
        //     let mut lemma = Vec::new();
        //     for &lit in self.cube.iter() {
        //         if solver.failed(lit.to_external()).unwrap() {
        //             lemma.push(-lit);
        //         }
        //     }
        //     if lemma.len() < self.cube.len() {
        //         // lemma.sort_by_key(|lit| lit.inner());
        //         // debug!("new lemma from unsat core: {}", DisplaySlice(&lemma));
        //         solver.add_clause(clause_to_external(&lemma));
        //     }
        // }
        res
    }
}

type TaskResult<Task> = (Task, SolveResponse, Duration);

pub type SolverPool<Task> = Pool<Task, TaskResult<Task>>;

pub fn new_solver_pool<Task, F, S>(size: usize, init: F, solve: S) -> SolverPool<Task>
where
    Task: Debug + Send + 'static,
    F: Fn(usize) -> Cadical,
    F: Send + Sync + 'static,
    S: Fn(&Task, &Cadical) -> SolveResponse,
    S: Send + Sync + 'static,
{
    debug!("Initializing SolverPool of size {}", size);
    let init = Arc::new(init);
    let solve = Arc::new(solve);
    Pool::new_with(size, move |i, task_receiver, result_sender| {
        let solver = init(i);
        for task in task_receiver {
            let time_solve = Instant::now();
            let res = solve(&task, &solver);
            let time_solve = time_solve.elapsed();
            trace!("{:?} in {:.1}s for {:?}", res, time_solve.as_secs_f64(), task);
            if result_sender.send((task, res, time_solve)).is_err() {
                break;
            }
        }
        debug!(
            "finished {:?}: conflicts = {}, decisions = {}, propagations = {}",
            thread::current().id(),
            solver.conflicts(),
            solver.decisions(),
            solver.propagations(),
        );
    })
}
