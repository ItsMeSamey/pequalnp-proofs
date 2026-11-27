# Independent original-input controls

Run python independent_controls.py. The tested source hashes are in independent-review.sha256 and per-configuration counts are in independent-review.log. Independent expression, CNF and dense affine-gate truth tables used original input cubes of size at most 16. Dense operands reused primary bits and intermediate gates. The deliberately expanded two-input presentation had 23 AND gates, plus a 25-gate contradictory variant. A separate 15,000-input affine readout checked the large-mask path without enumerating that cube.

All 121 inputs (94 SAT and 27 UNSAT) passed in seven configurations, giving 847 complete decisions. With cofactor rewriting enabled, the default chose affine output on 38 SAT/23 UNSAT, affine quotient on 51/4, and grouped masks on 5/0. With one backend requested and rewriting disabled, the common affine shortcut resolved 21 SAT/7 UNSAT in each configuration.

| Requested route | Backend SAT | Backend UNSAT | Fallback SAT | Fallback UNSAT |
|---|---:|---:|---:|---:|
| affine_quotient | 73 | 20 | 0 | 0 |
| backward_bank | 73 | 20 | 0 | 0 |
| reachable_span | 18 | 7 | 55 | 13 |
| grouped_mask | 72 | 17 | 1 | 3 |

With no routes or budget zero, each run used the same affine shortcuts and exhaustive search resolved 73 SAT/20 UNSAT. Every positive matched an independently identified original model and reported one original replay. Every exhaustive negative used exactly 2^raw_n evaluations. Separate direct backend probes used 45 expression trees and two budgets per backend, 360 calls in total; the log distinguishes solved cases and skips. Available backend counts were compared with exact original model counts.

Temporary mocks verified skip, unknown and timeout result codes, and TimeoutError in estimation and solving, all fall through to exact search. A different unrecognized status and three absent or corrupt SAT witness cases raised exceptions. A deliberately false backend UNSAT report was accepted: the dispatcher trusts each backend's negative decision and supplies no independent negative proof checker. A repeat run returned the same route and witness. Timings are diagnostic. The budget applies to backend selection/work rather than total runtime: preprocessing, estimation and the complete fallback can still run. These controls establish finite-corpus correctness, not a speedup theorem.
