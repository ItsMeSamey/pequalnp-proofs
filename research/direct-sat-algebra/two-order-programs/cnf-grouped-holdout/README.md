# Independent shuffled CNF holdout

Both complete pipelines matched exhaustive raw model counts on 28 of 28 cases (17 SAT, 11 UNSAT). All 34 returned SAT witnesses replayed on the original clauses. There were no omissions, errors or timeouts. The separate grouped entry decided 12 cases by affine reasoning, six SAT and six UNSAT. These were the K4, K3,3 and signed-ring controls. On all eight random/planted formulas and four mixed pinned relations it returned NO_COMMON_CLASS. Both wheel pairs exceeded its default arity three. The corpus therefore tests declines but supplies no direct positive evidence for the meet or majority branches.

| Measurement | Original complete | Grouped then original complete |
|---|---:|---:|
| Grouped attempts / decisive | 0 / 0 | 28 / 12 |
| Grouped table cells / generated | 0 / 0 | 2,192 / 72 |
| Original complete calls | 28 | 16 |
| Native fixed-order decisions | 20 | 12 |
| Original native charged cells | 688,270 | 564,647 |
| Original joint candidate rows | 922 | 449 |
| Exhaustive fallback assignments | 0 | 0 |
| Total subprocess seconds | 3.612 | 3.280 |

Timing includes startup and IPC and is descriptive only. The original exhaustive oracle ran separately. Each pipeline used its default backend bounds, with identical original complete-mode limits. The grouped entry adds preprocessing work. Per-attempt records preserve all returned work and verdicts. The same cases ran baseline then enhanced, sequentially, with no parameter tuning. See protocol.md and precommit.sha256 for the advance commitment and results.jsonl for full stage costs.
