use std::time::{Duration, Instant};

use ahash::{AHashMap, AHashSet};
use indicatif::ProgressIterator;
use itertools::zip_eq;
use log::{debug, info, trace};
use rand::distributions::{Bernoulli, Distribution};
use rand::prelude::*;

use crate::backdoor::Backdoor;
use crate::fitness::Fitness;
use crate::lit::Lit;
use crate::solvers::SatSolver;
// use crate::utils::*;
use crate::var::Var;

#[derive(Debug)]
pub struct BackdoorSearcher {
    pub solver: SatSolver,
    pub global_pool: Vec<Var>,
    pub banned_vars: AHashSet<Var>,
    pub rng: StdRng,
    pub cache: AHashMap<Vec<Var>, Fitness>,
    pub cache_hits: usize,
    pub cache_misses: usize,
    pub options: Options,
}

impl BackdoorSearcher {
    pub fn new(solver: SatSolver, pool: Vec<Var>, options: Options) -> Self {
        Self {
            solver,
            global_pool: pool,
            banned_vars: AHashSet::new(),
            rng: StdRng::seed_from_u64(options.seed),
            cache: AHashMap::new(),
            cache_hits: 0,
            cache_misses: 0,
            options,
        }
    }
}

#[derive(Debug)]
pub struct Options {
    pub seed: u64,
    pub ban_used_variables: bool,
}

pub const DEFAULT_OPTIONS: Options = Options {
    seed: 42,
    ban_used_variables: false,
};

impl Default for Options {
    fn default() -> Self {
        DEFAULT_OPTIONS
    }
}

#[derive(Debug)]
pub struct RunResult {
    pub best_iteration: usize,
    pub best_instance: Backdoor,
    pub best_fitness: Fitness,
    pub time: Duration,
    pub records: Vec<Record>,
}

#[derive(Debug)]
pub struct Record {
    pub iteration: usize,
    pub instance: Backdoor,
    pub fitness: Fitness,
    pub time: Duration,
}

impl BackdoorSearcher {
    pub fn run(
        &mut self,
        backdoor_size: usize,
        num_iter: usize,
        stagnation_limit: Option<usize>,
        timeout: Option<f64>,
        max_rho: Option<f64>,
        min_iter: usize,
        pool_limit: Option<usize>,
    ) -> Option<RunResult> {
        let start_time = Instant::now();

        info!("Running EA for {} iterations with backdoor size {}", num_iter, backdoor_size);

        // Keep only active variables in the pool:
        self.global_pool.retain(|&v| self.solver.is_active(v));
        // Construct the pool of variables:
        let mut pool = self.global_pool.clone();
        // Exclude banned variables from the pool:
        pool.retain(|v| !self.banned_vars.contains(v));

        // let mut top_score_vars = vars_from_external(self.solver.as_cadical().get_top_score_variables(1000).iter().copied());
        // top_score_vars.retain(|v| pool.contains(v));
        // pool = top_score_vars.into_iter().take(100).collect();

        debug!("Pool size: {}", pool.len());
        if pool.len() < backdoor_size {
            info!("Pool size is too small, skipping the run");
            return None;
        }

        assert!(
            pool.len() >= backdoor_size,
            "Pool size must be at least {}, but the pool contains only {} elements",
            backdoor_size,
            pool.len()
        );

        if let Some(pool_limit) = pool_limit {
            if pool.len() > pool_limit {
                debug!("Limiting the pool to {}...", pool_limit);
                let time_pool_limit = Instant::now();
                let mut heuristic = AHashMap::new();
                for &var in pool.iter().progress() {
                    let pos_lit = Lit::new(var, false);
                    let neg_lit = Lit::new(var, true);

                    let (_pos_res, pos_prop) = match &mut self.solver {
                        SatSolver::Cadical(solver) => solver.propcheck(&[pos_lit.to_external()], false, false, false),
                    };
                    let (_neg_res, neg_prop) = match &mut self.solver {
                        SatSolver::Cadical(solver) => solver.propcheck(&[neg_lit.to_external()], false, false, false),
                    };
                    let h = pos_prop * neg_prop;
                    // info!("Variable {} (literals {} and {}) has heuristic value: {} * {} = {}", var, pos_lit, neg_lit, pos_prop, neg_prop, h);
                    // debug!("{} => {} => {}", pos_lit, _pos_res, DisplaySlice(&pos_prop));
                    // debug!("{} => {} => {}", neg_lit, _neg_res, DisplaySlice(&neg_prop));
                    heuristic.insert(var, h);
                }
                debug!(
                    "Computed heuristic values for {} vars in {:.3} s",
                    pool.len(),
                    time_pool_limit.elapsed().as_secs_f64()
                );
                let mut hs: Vec<_> = heuristic.values().copied().collect();
                hs.sort();
                hs.reverse();
                assert!(hs.len() > pool_limit);
                let limit = hs[pool_limit - 1];
                debug!("limit = {}", limit);
                pool.retain(|v| heuristic[v] >= limit);
                debug!("pool.len() = {}", pool.len());
            }
        }

        let time_initial = Instant::now();

        // Create an initial instance:
        let mut instance = self.initial_instance(backdoor_size, &pool);
        debug!("Initial instance: {:#}", instance);

        // Evaluate the initial instance:
        let mut fitness = self.calculate_fitness(&instance, None);
        debug!("Initial fitness: {:?}", fitness);

        // Store the best result:
        let mut best_iteration: usize = 0;
        let mut best_instance = instance.clone();
        let mut best_fitness = fitness.clone();

        let time_initial = time_initial.elapsed();

        // Store all results:
        let mut records = Vec::new();
        records.push(Record {
            iteration: 0,
            instance: instance.clone(),
            fitness: fitness.clone(),
            time: time_initial,
        });

        // Count the stagnated iterations:
        let mut num_stagnation: usize = 0;

        for i in 1..=num_iter {
            let time_iter = Instant::now();

            // Break upon reaching the timeout:
            if let Some(timeout) = timeout {
                if start_time.elapsed().as_secs_f64() >= timeout {
                    debug!("Reached the timeout of {:.1} s", timeout);
                    break;
                }
            }

            // Break upon reaching the maximum required rho:
            if let Some(max_rho) = max_rho {
                if i > min_iter && best_fitness.rho >= max_rho {
                    debug!("Reached maximum required rho {} >= {}", best_fitness.rho, max_rho);
                    break;
                }
            }

            // Produce the new instance (either mutate the previous, or re-init):
            let mutated_instance = {
                let mut need_reinit = false;
                if let Some(stagnation_limit) = stagnation_limit {
                    if num_stagnation >= stagnation_limit {
                        need_reinit = true;
                    }
                }
                if need_reinit {
                    // Re-initialize:
                    num_stagnation = 0;
                    self.initial_instance(backdoor_size, &pool)
                } else {
                    // Mutate the instance:
                    let mut mutated_instance = instance.clone();
                    self.mutate(&mut mutated_instance, &pool);
                    mutated_instance
                }
            };

            // Evaluate the mutated instance:
            let mutated_fitness = self.calculate_fitness(&mutated_instance, Some(&best_fitness));

            let time_iter = time_iter.elapsed();
            if i <= 10 || (i < 1000 && i % 100 == 0) || (i < 10000 && i % 1000 == 0) || i % 10000 == 0 {
                debug!(
                    "[{} / {}] rho={:.3}, hard={}, size={}, time={:.3} ms",
                    i,
                    num_iter,
                    mutated_fitness.rho,
                    mutated_fitness.num_hard,
                    backdoor_size,
                    time_iter.as_secs_f64() * 1000.0
                );
            }

            // Save the record about the new instance:
            records.push(Record {
                iteration: i,
                instance: mutated_instance.clone(),
                fitness: mutated_fitness.clone(),
                time: time_iter,
            });

            // Update the best:
            if mutated_fitness < best_fitness {
                best_iteration = i;
                best_instance = mutated_instance.clone();
                best_fitness = mutated_fitness.clone();
            } else {
                num_stagnation += 1;
                trace!("Stagnated for {} iterations", num_stagnation);
            }

            // (1+1) strategy:
            if mutated_fitness <= fitness {
                instance = mutated_instance;
                fitness = mutated_fitness;
            }
        }

        // Print the best result:
        info!("Best iteration: {} / {}", best_iteration, num_iter);
        info!("Best instance: {:#}", best_instance);
        info!("Best fitness: {:?}", best_fitness);

        debug!("cache hits: {}", self.cache_hits);
        debug!("cache misses: {}", self.cache_misses);

        // Ban used variables:
        if self.options.ban_used_variables {
            self.banned_vars.extend(best_instance.variables.iter().cloned());
        }

        // Clear the cache:
        self.cache.clear();

        let elapsed_time = start_time.elapsed();
        info!("EA done in {:.3} s", elapsed_time.as_secs_f64());

        Some(RunResult {
            best_iteration,
            best_instance,
            best_fitness,
            time: elapsed_time,
            records,
        })
    }

    fn initial_instance(&mut self, size: usize, pool: &[Var]) -> Backdoor {
        Backdoor::new_random(size, pool, &mut self.rng)
    }

    fn calculate_fitness(&mut self, instance: &Backdoor, best: Option<&Fitness>) -> Fitness {
        let key = instance.get_variables();
        if let Some(fit) = self.cache.get(&key) {
            self.cache_hits += 1;
            fit.clone()
        } else {
            self.cache_misses += 1;
            let fit = calculate_fitness(instance, best, &self.solver);
            self.cache.insert(key, fit.clone());
            fit
        }
    }

    fn mutate(&mut self, instance: &mut Backdoor, pool: &[Var]) {
        mutate(instance, pool, &mut self.rng);
    }
}

fn calculate_fitness(instance: &Backdoor, best: Option<&Fitness>, solver: &SatSolver) -> Fitness {
    let vars = instance.get_variables();
    assert!(vars.len() < 32);

    // Compute rho:
    // let limit = 0;
    let limit = best.map_or(0, |b| b.num_hard + 1);
    let num_hard = solver.propcheck_all_tree(&vars, limit);
    let num_total = 1u64 << vars.len();
    let rho = 1.0 - (num_hard as f64 / num_total as f64);

    // Calculate the fitness value:
    let value = 1.0 - rho;

    Fitness { value, rho, num_hard }
}

fn mutate(instance: &mut Backdoor, pool: &[Var], rng: &mut impl Rng) {
    assert!(pool.len() >= instance.len());

    let n = instance.len();
    let m = pool.len() - n;
    if m >= n {
        let p = 1.0 / n as f64;
        let d = Bernoulli::new(p).unwrap();

        let mut to_replace = Vec::new();
        for i in 0..n {
            if d.sample(rng) {
                to_replace.push(i);
            }
        }
        // to_replace.len() ~ Bin(1/n)
        assert!(to_replace.len() <= n);

        let other_vars: Vec<Var> = pool.iter().filter(|v| !instance.variables.contains(v)).copied().collect();
        assert!(other_vars.len() >= to_replace.len());
        let substituted = other_vars.choose_multiple(rng, to_replace.len());
        for (i, &v) in zip_eq(to_replace, substituted) {
            instance.variables[i] = v;
        }
    } else {
        if m == 0 {
            return;
        }
        let p = 1.0 / m as f64;
        let d = Bernoulli::new(p).unwrap();

        let mut to_replace = Vec::new();
        for &v in pool.iter() {
            if instance.variables.contains(&v) {
                continue;
            }
            if d.sample(rng) {
                to_replace.push(v);
            }
        }
        // to_replace.len() ~ Bin(1/m)
        assert!(to_replace.len() <= m);

        let substituted = (0..instance.len()).choose_multiple(rng, to_replace.len());
        for (i, v) in zip_eq(substituted, to_replace) {
            instance.variables[i] = v;
        }
    }

    // Instance size must stay the same:
    assert_eq!(instance.len(), n);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mutate() {
        let n: usize = 10;
        for len in 1..=n {
            let mut rng = StdRng::seed_from_u64(42);
            let pool: Vec<Var> = (0..n).map(|i| Var::from_external(i as u32 + 1)).collect();

            let base = Backdoor::new(pool.choose_multiple(&mut rng, len).copied().collect());
            assert_eq!(base.len(), len);

            let mut instance = base.clone();
            mutate(&mut instance, &pool, &mut rng);
            assert_eq!(instance.len(), len);
        }
    }
}
