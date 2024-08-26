# Backdoor-based SAT Solver

> SAT solver based on rho-backdoors.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.13375121.svg)](https://doi.org/10.5281/zenodo.13375121)

## Instructions

```sh
git clone https://github.com/Lipen/backdoor-solver
cd backdoor-solver
git submodule update --init --recursive
```

## SAT solver

> SAT solver that interleaves CaDiCaL with clauses derivation procedures utilizing rho-backdoors.

### CLI Usage

```
Usage: interleave [OPTIONS] --backdoor-size <INT> --num-iters <INT> --max-product <INT> --budget-filter <INT> --budget-solve <INT> <CNF>

Arguments:
  <CNF>  Input file with CNF in DIMACS format

Options:
  -o, --output <FILE>
          Path to output file in DIMACS format. If the problem is SAT, contains two lines: "s SATISFIABLE\nv 1 2 ... 0\n", else contains a single line: "s UNSATISFIABLE" or "s INDET"
      --results <FILE>
          Path to a file with results
      --seed <INT>
          Random seed [default: 42]
      --backdoor-size <INT>
          Backdoor size
      --num-iters <INT>
          Number of EA iterations
      --stagnation-limit <INT>
          Number of stagnated iterations before re-initialization
      --ban-used
          Do ban variables used in the best backdoors on previous runs?
      --reset-used-vars
          Reset banned used variables on empty product
      --allow <INT...>
          Comma-separated list of allowed variables (1-based indices)
      --ban <INT...>
          Comma-separated list of banned variables (1-based indices)
      --derive-ternary
          Derive ternary clauses
      --max-product <INT>
          Maximum product size
      --use-sorted-filtering
          Use novel sorted filtering method
      --num-conflicts <INT>
          Number of conflicts (budget per task in filtering) [default: 1000]
      --budget-filter <INT>
          Initial budget (in conflicts) for filtering
      --factor-budget-filter <FLOAT>
          Multiplicative factor for filtering budget [default: 1]
      --budget-solve <INT>
          Initial budget (in conflicts) for solving
      --factor-budget-solve <FLOAT>
          Multiplicative factor for solving budget [default: 1]
      --budget-presolve <INT>
          Budget (in conflicts) for pre-solve [default: 0]
      --compute-cores
          Do compute cores for easy tasks and invalid cubes
      --add-cores
          Do add lemmas from cores
      --max-core-size <MAX_CORE_SIZE>
          Maximum core size to be added (0 = unlimited) [default: 0]
      --cadical-options <CADICAL_OPTIONS>
          Comma-separated list of Cadical options ('key=value' pairs, e.g. 'elim=0,ilb=0,check=1')
  -h, --help
          Print help
  -V, --version
          Print version
```

### Example

```sh
cargo run --release --bin interleave -- data/mult/lec_CvK_12x12.cnf --backdoor-size 10 --num-iters 10000 --ban-used --max-product 10000 --budget-filter 10000 --factor-budget-filter 1.1 --budget-solve 100000 --factor-budget-solve 1.1 --budget-presolve 10000 --output out.txt
```

## Backdoor Searcher

> Evolutionary algorithm for searching rho-backdoors for a given SAT formula.

### CLI Usage

```
Usage: search [OPTIONS] --backdoor-size <INT> --num-iters <INT> <CNF>

Arguments:
  <CNF>  Input file with CNF in DIMACS format

Options:
      --backdoor-size <INT>     Backdoor size
      --num-iters <INT>         Number of EA iterations
      --num-runs <INT>          Number of EA runs [default: 1]
  -o, --output <FILE>           Path to a output file with backdoors
      --seed <INT>              Random seed [default: 42]
      --allow <INT...>          Comma-separated list of allowed variables (1-based indices)
      --ban <INT...>            Comma-separated list of banned variables (1-based indices)
      --ban-used                Do ban variables used in best backdoors on previous runs?
      --stagnation-limit <INT>  Number of stagnated iterations before re-initialization
      --max-rho <FLOAT>         Maximum required rho value (break EA upon reaching) [default: 1]
      --min-iter <INT>          Minimum number of EA iterations [default: 0]
      --dump-records            Do dump records for each EA run?
      --derive                  Do derive clauses from backdoors?
      --dump-derived            Do dump derived clauses after each EA run?
      --probe                   Do probe the backdoor variables?
      --probe-derive            Do try to probe-derive all units and binary clauses?
      --derive-ternary          Derive ternary clauses
      --budget-presolve <INT>   Budget (in conflicts) for pre-solve [default: 0]
  -h, --help                    Print help
  -V, --version                 Print version

```

### Example

Search for 3 backdoors, each of size 10, using 1000 iterations of EA and the random seed 42 (default):

```sh
cargo run --release --bin search -- data/mult/lec_CvK_12.cnf --backdoor-size 10 --num-iters 1000 --num-runs 3 --seed 42 --output output.txt
```

`output.txt` might look like:
```
ackdoor [4242, 4919, 2082, 1920, 4969, 5082, 4903, 2163, 2154, 4071] of size 10 on iter 829 with fitness = 0.029296875, rho = 0.970703125, hard = 30 in 120.671 ms
Backdoor [5089, 3989, 3375, 4265, 2163, 4273, 2648, 4158, 2082, 3133] of size 10 on iter 935 with fitness = 0.009765625, rho = 0.990234375, hard = 10 in 99.219 ms
Backdoor [4022, 4034, 4475, 4383, 2606, 4902, 1895, 960, 3538, 2471] of size 10 on iter 884 with fitness = 0.013671875, rho = 0.986328125, hard = 14 in 70.435 ms
```

Note: variables in the reported backdoors (in file/console) are 1-based.
