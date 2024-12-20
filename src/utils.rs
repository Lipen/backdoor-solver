use std::collections::HashSet;
use std::ffi::OsStr;
use std::fmt::{Display, Formatter};
use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader, LineWriter, Write};
use std::path::Path;

use flate2::read::GzDecoder;
use itertools::{join, zip_eq, Itertools, MultiProduct};
use log::{debug, trace};

use cadical::statik::Cadical;
use cadical::SolveResponse;

use crate::lit::Lit;
use crate::trie::Trie;
use crate::var::Var;

pub struct DisplaySlice<'a, T>(pub &'a [T])
where
    &'a T: Display;

impl<'a, T> Display for DisplaySlice<'a, T>
where
    &'a T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", join(self.0, ", "))
    }
}

pub fn display_slice<T>(slice: impl AsRef<[T]>) -> String
where
    for<'a> &'a T: Display,
{
    format!("[{}]", join(slice.as_ref(), ", "))
}

pub fn display_iter_slices<T, I>(iter: I) -> String
where
    for<'a> &'a T: Display,
    I: IntoIterator,
    I::Item: AsRef<[T]>,
{
    format!("[{}]", iter.into_iter().map(|x| display_slice(x)).join(", "))
}

pub fn get_extension(path: &Path) -> Option<&str> {
    path.extension().and_then(OsStr::to_str)
}

pub fn read_maybe_gzip<P>(path: P) -> io::Result<Box<dyn BufRead>>
where
    P: AsRef<Path>,
{
    let path = path.as_ref();
    let file = File::open(path)?;
    let capacity = 128 * 1024;
    if get_extension(path).unwrap() == "gz" {
        Ok(Box::new(BufReader::with_capacity(capacity, GzDecoder::new(file))))
    } else {
        Ok(Box::new(BufReader::with_capacity(capacity, file)))
    }
}

pub fn parse_dimacs<P>(path: P) -> impl Iterator<Item = Vec<Lit>>
where
    P: AsRef<Path>,
{
    read_maybe_gzip(path).unwrap().lines().map_while(Result::ok).filter_map(|line| {
        if line.is_empty() {
            trace!("Skipping empty line");
            None
        } else if line.starts_with('c') {
            trace!("Skipping comment '{}'", line);
            None
        } else if line.starts_with('p') {
            trace!("Skipping header '{}'", line);
            None
        } else {
            let clause = parse_dimacs_clause(&line);
            Some(clause)
        }
    })
}

pub fn parse_dimacs_clause(s: &str) -> Vec<Lit> {
    let clause = s
        .split_whitespace()
        .map(|x| x.parse::<i32>().expect("could not parse lit in clause"))
        .collect_vec();
    let (&last, lits) = clause.split_last().unwrap();
    assert_eq!(last, 0, "last lit in clause must be 0");
    lits.iter().map(|&lit| Lit::from_external(lit)).collect()
}

pub fn parse_multiple_comma_separated_intervals_from<P: AsRef<Path>>(path: P) -> Vec<Vec<usize>> {
    let path = path.as_ref();
    debug!("Reading '{}'", path.display());
    let f = File::open(path).unwrap_or_else(|_| panic!("Could not open '{}'", path.display()));
    let f = BufReader::new(f);
    let mut result = Vec::new();
    for line in f.lines().map_while(Result::ok) {
        result.push(parse_comma_separated_intervals(&line));
    }
    result
}

pub fn parse_multiple_comma_separated_intervals(input: &str) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for part in input.split(':') {
        result.push(parse_comma_separated_intervals(part));
    }
    result
}

pub fn parse_comma_separated_intervals(input: &str) -> Vec<usize> {
    let mut result = Vec::new();
    for part in input.split(',') {
        let range_parts: Vec<&str> = part.splitn(2, '-').collect();
        if range_parts.len() == 2 {
            let start: usize = range_parts[0].parse().unwrap();
            let end: usize = range_parts[1].parse().unwrap();
            if start <= end {
                result.extend(start..=end);
            } else {
                result.extend((end..=start).rev());
            }
        } else {
            let single: usize = part.parse().unwrap();
            result.push(single);
        }
    }
    result
}

pub fn parse_key_value_pairs(input: &str) -> Vec<(&str, &str)> {
    let mut result = Vec::new();
    for part in input.split(',') {
        let parts: Vec<&str> = part.splitn(2, '=').collect();
        if parts.len() == 2 {
            result.push((parts[0], parts[1]))
        } else {
            panic!("Invalid key-value pair: '{}'", part)
        }
    }
    result
}

pub fn get_hard_tasks(variables: &[Var], solver: &Cadical) -> Vec<Vec<Lit>> {
    let vars_external: Vec<i32> = variables.iter().map(|var| var.to_external() as i32).collect();
    // let res = solver.propcheck_all_tree(&vars_external, 0, true);
    // let valid = solver.propcheck_all_tree_get_valid();
    let mut valid = Vec::new();
    let res = solver.propcheck_all_tree_via_internal(&vars_external, 0, Some(&mut valid), None);
    assert_eq!(valid.len(), res as usize);
    valid
        .into_iter()
        .map(|cube| cube.into_iter().map(|i| Lit::from_external(i)).collect())
        .collect()
}

pub fn partition_tasks_cadical(variables: &[Var], solver: &Cadical) -> (Vec<Vec<Lit>>, Vec<Vec<Lit>>) {
    partition_tasks_with(variables, |cube| {
        let cube: Vec<i32> = cube.iter().map(|lit| lit.to_external()).collect();
        // Note: `restore = false` is UNSAFE in general, but since the variables are active, it should be safe.
        let (res, _num_prop) = solver.propcheck(&cube, false, false, false);
        res
    })
}

pub fn partition_tasks_cadical_emulated(variables: &[Var], solver: &Cadical) -> (Vec<Vec<Lit>>, Vec<Vec<Lit>>) {
    partition_tasks_with(variables, |cube| {
        let cube: Vec<i32> = cube.iter().map(|lit| lit.to_external()).collect();
        for &lit in cube.iter() {
            solver.assume(lit).unwrap();
        }
        solver.limit("conflicts", 1);
        match solver.solve().unwrap() {
            SolveResponse::Sat => unreachable!(),
            SolveResponse::Unsat => {
                // log::info!("UNSAT on cube {}", DisplaySlice(&cube));
                false
            }
            SolveResponse::Interrupted => {
                // log::info!("UNKNOWN on cube {}", DisplaySlice(&cube));
                true
            }
        }
    })
}

pub fn partition_tasks_with<F>(variables: &[Var], mut propcheck: F) -> (Vec<Vec<Lit>>, Vec<Vec<Lit>>)
where
    F: FnMut(&[Lit]) -> bool,
{
    let mut hard = Vec::new();
    let mut easy = Vec::new();

    for cube in product_repeat([true, false].into_iter(), variables.len()) {
        let assumptions = zip_eq(variables, cube).map(|(&v, s)| Lit::new(v, s)).collect_vec();
        let result = propcheck(&assumptions);
        if result {
            hard.push(assumptions);
        } else {
            easy.push(assumptions);
        }
    }

    (hard, easy)
}

/// Rust version of Python's `itertools.product()`.
/// It returns the cartesian product of the input iterables, and it is
/// semantically equivalent to `repeat` nested for loops.
///
/// # Arguments
///
/// * `it` - An iterator over a cloneable data structure
/// * `repeat` - Number of repetitions of the given iterator
///
/// See https://stackoverflow.com/a/68231315/3592218
pub fn product_repeat<I>(it: I, repeat: usize) -> MultiProduct<I>
where
    I: Iterator + Clone,
    I::Item: Clone,
{
    std::iter::repeat(it).take(repeat).multi_cartesian_product()
}

pub fn concat_cubes(a: Vec<Lit>, b: Vec<Lit>) -> Vec<Lit> {
    let mut r = HashSet::new();
    r.extend(a);
    r.extend(b);
    let mut r = r.into_iter().collect_vec();
    r.sort_by_key(|lit| lit.inner());
    r
    // let mut r = Vec::new();
    // r.extend(a);
    // for x in b {
    //     if !r.contains(&x) {
    //         r.push(x);
    //     }
    // }
    // r
}

pub fn bits_to_number(bits: &[bool]) -> u32 {
    let mut result: u32 = 0;
    for &bit in bits.iter() {
        result <<= 1;
        result |= bit as u32;
    }
    result
}

pub fn gray_to_index(bits: &[bool]) -> u32 {
    let mut num = bits_to_number(bits);
    num ^= num >> 16;
    num ^= num >> 8;
    num ^= num >> 4;
    num ^= num >> 2;
    num ^= num >> 1;
    num
}

pub fn mask(base: &[Lit], data: &[Lit]) -> Vec<bool> {
    let base = base.iter().map(|lit| lit.var()).collect::<HashSet<_>>();
    data.iter().map(|lit| !base.contains(&lit.var())).collect()
}

pub fn determine_vars_pool<P: AsRef<Path>>(path: P, allowed_vars: &Option<String>, banned_vars: &Option<String>) -> Vec<Var> {
    // Determine the set of variables encountered in CNF:
    let mut encountered_vars = HashSet::new();
    for clause in parse_dimacs(path) {
        for lit in clause {
            encountered_vars.insert(lit.var());
        }
    }

    // Ban some variables:
    if let Some(banned_vars) = banned_vars {
        let chunks = if let Some(banned_vars) = banned_vars.strip_prefix('@') {
            parse_multiple_comma_separated_intervals_from(banned_vars)
        } else {
            parse_multiple_comma_separated_intervals(banned_vars)
        };
        let banned_vars: HashSet<Var> = chunks.into_iter().flatten().map(|i| Var::from_external(i as u32)).collect();
        encountered_vars.retain(|v| !banned_vars.contains(v));
    }

    // Allow only some variables:
    if let Some(allowed_vars) = allowed_vars {
        let chunks = if let Some(allowed_vars) = allowed_vars.strip_prefix('@') {
            parse_multiple_comma_separated_intervals_from(allowed_vars)
        } else {
            parse_multiple_comma_separated_intervals(allowed_vars)
        };
        let allowed_vars: HashSet<Var> = chunks.into_iter().flatten().map(|i| Var::from_external(i as u32)).collect();
        encountered_vars.retain(|v| allowed_vars.contains(v));
    }

    // Create the pool of variables:
    let pool: Vec<Var> = encountered_vars.into_iter().sorted().collect();
    pool
}

pub fn create_line_writer<P: AsRef<Path>>(path: P) -> LineWriter<File> {
    let path = path.as_ref();
    let f = File::create(path).unwrap_or_else(|_| panic!("Could not create '{}'", path.display()));
    let f = LineWriter::new(f);
    f
}

pub fn maybe_create<P: AsRef<Path>>(path: &Option<P>) -> Option<LineWriter<File>> {
    path.as_ref().map(create_line_writer)
}

pub fn lits_to_external<'a, I>(lits: I) -> Vec<i32>
where
    I: IntoIterator<Item = &'a Lit>,
{
    lits.into_iter().map(|lit| lit.to_external()).collect()
}

pub fn lits_from_external<I>(lits: I) -> Vec<Lit>
where
    I: IntoIterator,
    I::Item: Into<i32>,
{
    lits.into_iter().map(|lit| Lit::from_external(lit.into())).collect()
}

pub fn vars_to_external<'a, I>(vars: I) -> Vec<i32>
where
    I: IntoIterator<Item = &'a Var>,
{
    vars.into_iter().map(|v| v.to_external() as i32).collect()
}

pub fn vars_from_external<I>(vars: I) -> Vec<Var>
where
    I: IntoIterator,
    I::Item: Into<i32>,
{
    vars.into_iter().map(|v| Var::from_external(v.into() as u32)).collect()
}

pub fn propcheck_all_trie_via_internal(
    solver: &Cadical,
    vars: &[Var],
    trie: &Trie,
    limit: u64,
    mut out_valid: Option<&mut Vec<Vec<Lit>>>,
    mut out_invalid: Option<&mut Vec<Vec<Lit>>>,
) -> u64 {
    // TODO:
    // if (internal->unsat || internal->unsat_constraint) {
    //     std::cout << "Already unsat" << std::endl;
    //     return 0;
    // }

    // Trivial case:
    if vars.is_empty() || trie.is_empty() {
        return 0;
    }

    // Backtrack to 0 level before prop-checking:
    if solver.internal_level() > 0 {
        trace!("Backtracking from level {} to 0", solver.internal_level());
        solver.internal_backtrack(0);
    }

    // Propagate everything that needs to be propagated:
    if !solver.internal_propagate() {
        debug!("Conflict during pre-propagation");
        solver.internal_reset_conflict();
        return 0;
    }

    // // Freeze variables:
    // for &var in vars.iter() {
    //     solver.freeze(var.to_external() as i32).unwrap();
    // }

    let mut cube = vec![false; vars.len()];
    let mut total_checked = 0u64;
    let mut total_count = 0u64;

    #[derive(Debug)]
    enum State {
        Descending,
        Ascending,
        Propagating,
    }
    let mut state = State::Descending;

    loop {
        let level = solver.internal_level();
        assert!(level <= vars.len());

        match state {
            State::Descending => {
                if level == vars.len() {
                    if let Some(valid) = &mut out_valid {
                        valid.push(zip_eq(vars, &cube).map(|(&v, &s)| Lit::new(v, s)).collect());
                    }
                    total_count += 1;
                    if limit > 0 && total_count >= limit {
                        trace!("reached the limit: {} >= {}", total_count, limit);
                        break;
                    }
                    state = State::Ascending;
                } else {
                    if trie.search_iter(cube.iter().take(level + 1).copied()) == 0 {
                        // Dummy level:
                        solver.internal_assume_decision(0);
                        state = State::Ascending;
                    } else {
                        let v = vars[level].to_external() as i32;
                        let lit = if cube[level] { -v } else { v };
                        let b = solver.internal_val(lit);
                        if b > 0 {
                            // Dummy level:
                            solver.internal_assume_decision(0);
                            state = State::Descending;
                        } else if b < 0 {
                            // Dummy level:
                            solver.internal_assume_decision(0);
                            // Conflicting assignment:
                            if let Some(invalid) = &mut out_invalid {
                                invalid.push(zip_eq(vars, &cube).take(level + 1).map(|(&v, &s)| Lit::new(v, s)).collect());
                            }
                            state = State::Ascending;
                        } else {
                            // Enqueue the literal:
                            solver.internal_assume_decision(lit);
                            state = State::Propagating;
                        }
                    }
                }
            }

            State::Ascending => {
                assert!(level > 0);

                // Find the 1-based index of the last 'false' value in 'cube':
                let mut i = level; // 1-based
                while i > 0 && cube[i - 1] {
                    i -= 1;
                }
                if i == 0 {
                    break;
                }

                // Increment the 'cube':
                assert!(!cube[i - 1]);
                cube[i - 1] = true;
                for j in i..vars.len() {
                    cube[j] = false;
                }

                // Backtrack to the level before `i`:
                solver.internal_backtrack(i - 1);

                // Switch state to descending:
                state = State::Descending;
            }

            State::Propagating => {
                total_checked += 1;
                if !solver.internal_propagate() {
                    // Conflict.
                    if let Some(invalid) = &mut out_invalid {
                        invalid.push(
                            zip_eq(vars, &cube)
                                .take(level)
                                .map(|(&v, &s)| Lit::new(v, s))
                                // .filter(|&lit| solver.internal_failed(lit.to_external()))
                                .collect(),
                        );
                    }
                    solver.internal_reset_conflict();
                    state = State::Ascending;
                } else {
                    // No conflict.
                    state = State::Descending;
                }
            }
        }
    }

    // Post-backtrack to zero level:
    solver.internal_backtrack(0);

    // // Melt variables:
    // for &var in vars.iter() {
    //     solver.melt(var.to_external() as i32).unwrap();
    // }

    trace!("Checked {} cubes, found {} valid", total_checked, total_count);
    total_count
}

pub fn write_clause(f: &mut impl Write, lits: &[Lit]) -> io::Result<()> {
    for lit in lits.iter() {
        write!(f, "{} ", lit)?;
    }
    writeln!(f, "0")
}

#[cfg(test)]
mod tests {
    use itertools::assert_equal;
    use log::info;
    use test_log::test;

    use super::*;
    use crate::trie::build_trie;

    #[test]
    fn test_gray_to_number() {
        assert_eq!(0, gray_to_index(&[false, false, false, false]));
        assert_eq!(1, gray_to_index(&[false, false, false, true]));
        assert_eq!(2, gray_to_index(&[false, false, true, true]));
        assert_eq!(3, gray_to_index(&[false, false, true, false]));
        assert_eq!(4, gray_to_index(&[false, true, true, false]));
        assert_eq!(5, gray_to_index(&[false, true, true, true]));
        assert_eq!(6, gray_to_index(&[false, true, false, true]));
        assert_eq!(7, gray_to_index(&[false, true, false, false]));
        assert_eq!(8, gray_to_index(&[true, true, false, false]));
        assert_eq!(9, gray_to_index(&[true, true, false, true]));
        assert_eq!(10, gray_to_index(&[true, true, true, true]));
        assert_eq!(11, gray_to_index(&[true, true, true, false]));
        assert_eq!(12, gray_to_index(&[true, false, true, false]));
        assert_eq!(13, gray_to_index(&[true, false, true, true]));
        assert_eq!(14, gray_to_index(&[true, false, false, true]));
        assert_eq!(15, gray_to_index(&[true, false, false, false]));
    }

    #[test]
    fn test_mask() {
        let x1 = Lit::from_external(1);
        let x2 = Lit::from_external(2);
        let x3 = Lit::from_external(3);
        let x5 = Lit::from_external(5);
        let x7 = Lit::from_external(7);
        let x8 = Lit::from_external(8);
        let x9 = Lit::from_external(9);
        assert_equal(
            mask(&[x1, x2, x3, x7, x9], &[x2, x3, x5, x7, x8]),
            [false, false, true, false, true],
        )
    }

    #[test]
    fn test_cadical_propcheck() {
        let solver = Cadical::new();

        let x1 = 1;
        let x2 = 2;
        let g1 = 3;
        info!("x1 = {}, x2 = {}, g1 = {}", x1, x2, g1);

        // g1 <=> x1 AND x2
        solver.add_clause([g1, -x1, -x2]);
        solver.add_clause([-g1, x1]);
        solver.add_clause([-g1, x2]);

        // Forbid (x1 AND ~x2)
        solver.add_clause([-x1, x2]);

        info!("vars = {}, clauses = {}", solver.vars(), solver.irredundant());

        // Problem is satisfiable.
        // let res = solver.solve();
        // assert_eq!(res, SolveResult::Sat);

        let vars = vec![x1, x2];

        info!("----------------------");
        let count_tree = solver.propcheck_all_tree(&vars, 0, None);
        info!("count_tree = {}", count_tree);

        info!("----------------------");
        let mut valid_tree = Vec::new();
        let count_tree_internal = solver.propcheck_all_tree_via_internal(&vars, 0, Some(&mut valid_tree), None);
        info!("count_tree_internal = {}", count_tree_internal);
        assert_eq!(count_tree_internal, valid_tree.len() as u64);

        assert_eq!(count_tree, count_tree_internal);

        info!("----------------------");
        let variables = vars.iter().map(|&v| Var::from_external(v as u32)).collect::<Vec<_>>();
        let cubes = vec![vec![false, false], vec![true, true], vec![true, false], vec![false, true]];
        let trie = build_trie(&cubes);
        let mut valid_trie = Vec::new();
        let count_trie_internal = propcheck_all_trie_via_internal(&solver, &variables, &trie, 0, Some(&mut valid_trie), None);
        info!("count_trie_internal = {}", count_trie_internal);
        assert_eq!(count_trie_internal, valid_trie.len() as u64);

        assert_eq!(count_tree_internal, count_trie_internal);
    }
}
