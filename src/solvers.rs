use cadical::statik::Cadical;
use cadical::FixedResponse;

use crate::lit::Lit;
use crate::utils::*;
use crate::var::Var;

#[derive(Debug)]
pub enum SatSolver {
    Cadical(Cadical),
}

impl SatSolver {
    pub fn new_cadical(solver: Cadical) -> Self {
        SatSolver::Cadical(solver)
    }
}

impl SatSolver {
    pub fn num_vars(&self) -> u64 {
        match self {
            SatSolver::Cadical(solver) => solver.vars() as u64,
        }
    }

    pub fn is_already_assigned(&self, var: Var) -> bool {
        match self {
            SatSolver::Cadical(solver) => {
                let lit = var.to_external() as i32;
                solver.fixed(lit).unwrap() != FixedResponse::Unclear
            }
        }
    }

    pub fn is_active(&self, var: Var) -> bool {
        match self {
            SatSolver::Cadical(solver) => {
                let lit = var.to_external() as i32;
                solver.is_active(lit)
            }
        }
    }

    pub fn add_clause(&self, lits: &[Lit]) {
        match self {
            SatSolver::Cadical(solver) => {
                let clause = lits_to_external(lits);
                solver.add_clause(clause);
                // solver.add_derived_clause(clause);
            }
        }
    }

    pub fn propcheck_all_tree(&self, vars: &[Var], limit: u64) -> u64 {
        match self {
            SatSolver::Cadical(solver) => {
                let vars_external = vars_to_external(vars);
                // solver.propcheck_all_tree(&vars_external, limit, false)
                solver.propcheck_all_tree_via_internal(&vars_external, limit, None, None)
            }
        }
    }
}

impl SatSolver {
    pub fn as_cadical(&self) -> &Cadical {
        match self {
            SatSolver::Cadical(solver) => solver,
        }
    }
}
