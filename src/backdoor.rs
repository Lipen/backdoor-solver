use std::fmt::{Display, Formatter};

use itertools::Itertools;
use rand::prelude::*;

use crate::utils::display_slice;
use crate::var::Var;

#[derive(Debug, Clone)]
pub struct Backdoor {
    pub(crate) variables: Vec<Var>,
}

impl Backdoor {
    pub fn new(variables: Vec<Var>) -> Self {
        Self { variables }
    }

    pub fn new_random<R: Rng + ?Sized>(size: usize, pool: &[Var], rng: &mut R) -> Self {
        assert!(
            pool.len() >= size,
            "Pool must be at least of size {}, but has only {} elements",
            size,
            pool.len()
        );
        let variables = pool.choose_multiple(rng, size).copied().collect();
        Self::new(variables)
    }
}

impl Display for Backdoor {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let vars = self.get_variables();
        write!(f, "{}", display_slice(&vars))
    }
}

impl Backdoor {
    pub fn get_variables(&self) -> Vec<Var> {
        self.variables.iter().sorted().copied().collect()
    }

    pub fn len(&self) -> usize {
        self.variables.len()
    }

    // pub fn variables(&self) -> &[Var] {
    //     &self.variables
    // }
    // pub fn variables_mut(&mut self) -> &mut [Var] {
    //     &mut self.variables
    // }
}

// impl Index<usize> for Instance {
//     type Output = Var;
//
//     fn index(&self, index: usize) -> &Self::Output {
//         &self.variables[index]
//     }
// }
//
// impl IndexMut<usize> for Instance {
//     fn index_mut(&mut self, index: usize) -> &mut Self::Output {
//         &mut self.variables[index]
//     }
// }
