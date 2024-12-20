use std::collections::HashMap;

use indicatif::{ProgressBar, ProgressIterator, ProgressStyle};
use itertools::{zip_eq, Itertools};
use log::{debug, trace};

use crate::lit::Lit;
use crate::utils::display_slice;

// TODO: derive_units
// TODO: derive_binary
// TODO: derive_ternary

pub fn derive_clauses(hard: &[Vec<Lit>], derive_ternary: bool) -> Vec<Vec<Lit>> {
    trace!("derive_clauses(hard = [{}])", hard.iter().map(|c| display_slice(c)).join(", "));

    // Trivial case:
    if hard.is_empty() {
        return vec![];
    }

    for cube in hard.iter() {
        assert_eq!(cube.len(), hard[0].len());
        assert!(zip_eq(cube, &hard[0]).all(|(a, b)| a.var() == b.var()));
    }

    let n = hard[0].len();
    let mut derived_clauses = Vec::new();

    let pb = ProgressBar::new(n as u64);
    pb.set_style(
        ProgressStyle::with_template("{spinner:.green} [{elapsed}] [{bar:40.cyan/white}] {pos:>6}/{len} (ETA: {eta}) {msg}")
            .unwrap()
            .progress_chars("#>-"),
    );
    pb.set_message("units");
    // count_unit :: {i: (pos,neg)}
    let count_unit: HashMap<usize, (u64, u64)> = (0..n)
        // .into_par_iter()
        .progress_with(pb)
        .map(|i| {
            let mut pos = 0;
            let mut neg = 0;
            for cube in hard.iter() {
                if cube[i].negated() {
                    neg += 1;
                } else {
                    pos += 1;
                }
            }
            (i, (pos, neg))
        })
        .collect();

    for (&i, &(pos, neg)) in count_unit.iter() {
        let var = hard[0][i].var();
        debug!("Count (pos/neg) for {} is {} / {}", var, pos, neg);
    }
    for (&i, &(pos, neg)) in count_unit.iter() {
        let var = hard[0][i].var();
        if pos == 0 {
            let clause = vec![Lit::new(var, true)];
            debug!("variable {} is never positive |= clause {}", var, display_slice(&clause));
            derived_clauses.push(clause);
        }
        if neg == 0 {
            let clause = vec![Lit::new(var, false)];
            debug!("variable {} is never negative |= clause {}", var, display_slice(&clause));
            derived_clauses.push(clause);
        }
    }

    let pb = ProgressBar::new((n * (n - 1) / 2) as u64);
    pb.set_style(
        ProgressStyle::with_template("{spinner:.green} [{elapsed}] [{bar:40.cyan/white}] {pos:>6}/{len} (ETA: {eta}) {msg}")
            .unwrap()
            .progress_chars("#>-"),
    );
    pb.set_message("binary");
    // count_binary :: {(i,j): (++, +-, -+, --)}
    let count_binary: HashMap<(usize, usize), (u64, u64, u64, u64)> = (0..n)
        .tuple_combinations()
        // .par_bridge()
        .progress_with(pb)
        .filter_map(|(i, j)| {
            // Skip units:
            let (pos, neg) = count_unit[&i];
            if pos == 0 || neg == 0 {
                return None;
            }
            let (pos, neg) = count_unit[&j];
            if pos == 0 || neg == 0 {
                return None;
            }

            // Count pairs:
            let (mut pp, mut pn, mut np, mut nn) = (0, 0, 0, 0);
            for cube in hard.iter() {
                match (cube[i].negated(), cube[j].negated()) {
                    (false, false) => pp += 1, // pos-pos
                    (false, true) => pn += 1,  // pos-neg
                    (true, false) => np += 1,  // neg-pos
                    (true, true) => nn += 1,   // neg-neg
                };
            }
            Some(((i, j), (pp, pn, np, nn)))
        })
        .collect();

    for (&(i, j), &(pp, pn, np, nn)) in count_binary.iter() {
        let a = hard[0][i].var();
        let b = hard[0][j].var();
        debug!("Count (pp/pn/np/nn) for {}-{} is {} / {} / {} / {}", a, b, pp, pn, np, nn);
    }
    for (&(i, j), &(pp, pn, np, nn)) in count_binary.iter() {
        let a = hard[0][i].var();
        let b = hard[0][j].var();
        if pp == 0 {
            let clause = vec![Lit::new(a, true), Lit::new(b, true)];
            debug!("pair {}-{} is never pos-pos |= clause {}", a, b, display_slice(&clause));
            derived_clauses.push(clause);
        }
        if pn == 0 {
            let clause = vec![Lit::new(a, true), Lit::new(b, false)];
            debug!("pair {}-{} is never pos-neg |= clause {}", a, b, display_slice(&clause));
            derived_clauses.push(clause);
        }
        if np == 0 {
            let clause = vec![Lit::new(a, false), Lit::new(b, true)];
            debug!("pair {}-{} is never neg-pos |= clause {}", a, b, display_slice(&clause));
            derived_clauses.push(clause);
        }
        if nn == 0 {
            let clause = vec![Lit::new(a, false), Lit::new(b, false)];
            debug!("pair {}-{} is never neg-neg |= clause {}", a, b, display_slice(&clause));
            derived_clauses.push(clause);
        }
    }

    if derive_ternary {
        let pb = ProgressBar::new((n * (n - 1) * (n - 2) / 6) as u64);
        pb.set_style(
            ProgressStyle::with_template("{spinner:.green} [{elapsed}] [{bar:40.cyan/white}] {pos:>6}/{len} (ETA: {eta}) {msg}")
                .unwrap()
                .progress_chars("#>-"),
        );
        pb.set_message("ternary");
        // count_ternary :: {(i,j,k): (+++, ++-, +-+, +--, -++, -+-, --+, ---)}
        let count_ternary: HashMap<(usize, usize, usize), [u64; 8]> = (0..n)
            .tuple_combinations()
            // .par_bridge()
            .progress_with(pb)
            .filter_map(|(i, j, k)| {
                // Skip units:
                let (pos, neg) = count_unit[&i];
                if pos == 0 || neg == 0 {
                    return None;
                }
                let (pos, neg) = count_unit[&j];
                if pos == 0 || neg == 0 {
                    return None;
                }
                let (pos, neg) = count_unit[&k];
                if pos == 0 || neg == 0 {
                    return None;
                }

                // Skip binary:
                let (pp, pn, np, nn) = count_binary[&(i, j)];
                if pp == 0 || pn == 0 || np == 0 || nn == 0 {
                    return None;
                }
                let (pp, pn, np, nn) = count_binary[&(i, k)];
                if pp == 0 || pn == 0 || np == 0 || nn == 0 {
                    return None;
                }
                let (pp, pn, np, nn) = count_binary[&(j, k)];
                if pp == 0 || pn == 0 || np == 0 || nn == 0 {
                    return None;
                }

                // Count triples:
                let (mut ppp, mut ppn, mut pnp, mut pnn, mut npp, mut npn, mut nnp, mut nnn) = (0, 0, 0, 0, 0, 0, 0, 0);
                for cube in hard.iter() {
                    match (cube[i].negated(), cube[j].negated(), cube[k].negated()) {
                        (false, false, false) => ppp += 1, // pos-pos-pos
                        (false, false, true) => ppn += 1,  // pos-pos-neg
                        (false, true, false) => pnp += 1,  // pos-neg-pos
                        (false, true, true) => pnn += 1,   // pos-neg-neg
                        (true, false, false) => npp += 1,  // neg-pos-pos
                        (true, false, true) => npn += 1,   // neg-pos-neg
                        (true, true, false) => nnp += 1,   // neg-neg-pos
                        (true, true, true) => nnn += 1,    // neg-neg-neg
                    };
                }
                Some(((i, j, k), [ppp, ppn, pnp, pnn, npp, npn, nnp, nnn]))
            })
            .collect();

        for (&(i, j, k), &[ppp, ppn, pnp, pnn, npp, npn, nnp, nnn]) in count_ternary.iter() {
            let a = hard[0][i].var();
            let b = hard[0][j].var();
            let c = hard[0][k].var();
            debug!(
                "Count (ppp/ppn/pnp/pnn/npp/npn/nnp/nnn) for {}-{}-{} is {} / {} / {} / {} / {} / {} / {} / {}",
                a, b, c, ppp, ppn, pnp, pnn, npp, npn, nnp, nnn
            );
        }
        for (&(i, j, k), &[ppp, ppn, pnp, pnn, npp, npn, nnp, nnn]) in count_ternary.iter() {
            let a = hard[0][i].var();
            let b = hard[0][j].var();
            let c = hard[0][k].var();
            if ppp == 0 {
                let clause = vec![Lit::new(a, true), Lit::new(b, true), Lit::new(c, true)];
                debug!("triple {}-{}-{} is never pos-pos-pos |= clause {}", a, b, c, display_slice(&clause));
                derived_clauses.push(clause);
            }
            if ppn == 0 {
                let clause = vec![Lit::new(a, true), Lit::new(b, true), Lit::new(c, false)];
                debug!("triple {}-{}-{} is never pos-pos-neg |= clause {}", a, b, c, display_slice(&clause));
                derived_clauses.push(clause);
            }
            if pnp == 0 {
                let clause = vec![Lit::new(a, true), Lit::new(b, false), Lit::new(c, true)];
                debug!("triple {}-{}-{} is never pos-neg-pos |= clause {}", a, b, c, display_slice(&clause));
                derived_clauses.push(clause);
            }
            if pnn == 0 {
                let clause = vec![Lit::new(a, true), Lit::new(b, false), Lit::new(c, false)];
                debug!("triple {}-{}-{} is never pos-neg-neg |= clause {}", a, b, c, display_slice(&clause));
                derived_clauses.push(clause);
            }
            if npp == 0 {
                let clause = vec![Lit::new(a, false), Lit::new(b, true), Lit::new(c, true)];
                debug!("triple {}-{}-{} is never neg-pos-pos |= clause {}", a, b, c, display_slice(&clause));
                derived_clauses.push(clause);
            }
            if npn == 0 {
                let clause = vec![Lit::new(a, false), Lit::new(b, true), Lit::new(c, false)];
                debug!("triple {}-{}-{} is never neg-pos-neg |= clause {}", a, b, c, display_slice(&clause));
                derived_clauses.push(clause);
            }
            if nnp == 0 {
                let clause = vec![Lit::new(a, false), Lit::new(b, false), Lit::new(c, true)];
                debug!("triple {}-{}-{} is never neg-neg-pos |= clause {}", a, b, c, display_slice(&clause));
                derived_clauses.push(clause);
            }
            if nnn == 0 {
                let clause = vec![Lit::new(a, false), Lit::new(b, false), Lit::new(c, false)];
                debug!("triple {}-{}-{} is never neg-neg-neg |= clause {}", a, b, c, display_slice(&clause));
                derived_clauses.push(clause);
            }
        }
    }

    // Sort each clause:
    for clause in derived_clauses.iter_mut() {
        clause.sort_by_key(|lit| lit.inner());
    }
    // Sort all clauses:
    derived_clauses.sort_by_key(|clause| (clause.len(), clause.iter().map(|lit| lit.inner()).collect_vec()));

    derived_clauses
}
