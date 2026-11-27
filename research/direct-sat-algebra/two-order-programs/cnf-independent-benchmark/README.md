# Precommitted complete-mode original-CNF benchmark

The corpus and run policy were frozen before running the dispatcher. The precommit manifest digest was 081e9c8c39b702e3e100aa9c06cd4dc2cfd49c6065fe3d1ee0a9edc5bd0de44d. The dispatcher was combined_cnf.py at 69313d1591ef2ceaa406268f624ecedc97ae99bbeb36a709f86e5d7541b42283. Every executed query used complete=True and documented defaults: 250,000 cells, rank cap 32, 100,000 peel steps, 10,000 cell pairs and 10,000,000 linear-work units. No shared budget is exposed. Zero fallback_limit does not limit the exhaustive fallback in complete mode.

| Family | Precommitted | Executed | SAT | UNSAT | Omitted | Solver wall (ms) |
|---|---:|---:|---:|---:|---:|---:|
| Random 3CNF at 4.27n | 24 | 24 | 21 | 3 | 0 | 1197.3 |
| Prism parity | 8 | 4 | 2 | 2 | 4 | 233.6 |
| Pigeonhole | 8 | 4 | 2 | 2 | 4 | 26.4 |
| Grid, pinned and unpinned | 6 | 6 | 3 | 3 | 0 | 2.2 |

Every one of the 38 completed decisions matched independent evidence. All 28 positive witnesses satisfied the original signed clauses. Original cube enumeration was used only through 12 variables. Larger parity/pigeonhole formulas were omitted under the precommit rule against unguarded exhaustive fallback. The larger binary grids were eligible because the source SCC route is guaranteed. No case timed out. The native stage received 30 cases after 30 source skips and decided 24 SAT and six UNSAT by its fixed-order route. Source SCC decided the other four SAT and four UNSAT. Exhaustive fallback tried zero assignments. Across native attempts the logged factor compilers charged 752,611 cells and joint tests 1,245 candidate rows. These are different work units. The raw log retains allocations, all attempts, route-specific counters and timings. Source-stage timings are available but no source work-unit counter is supplied by the dispatcher.

Aggregate solver-clock time was 1.460 s; aggregate child-process turnaround including import and IPC was 2.871 s. These observations came from one sequential run under a 3 s/case cap, not a cross-solver performance comparison. The cohort is small and fixed; it did not exercise positive fallback usage. Omitted cases have independent family evidence, not observed solver verdicts.

Files: corpus.py and protocol.md define the frozen cohort and resource rules; oracle.py gives original witness checks and independent small truth tables; run.py executes sequentially; results.jsonl records every selected or omitted instance.
