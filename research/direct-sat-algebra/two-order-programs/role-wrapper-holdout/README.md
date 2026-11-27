# Guard-role wrapper holdout

Default wrapper decided all 22 new precommitted instances correctly (11 SAT, 11 UNSAT). Original numeric role recognition rejected 19 with multiple guards, including all six overlapping tetrahedron controls. It decided the other three. All returned SAT assignments replayed on the original unmodified raw clauses.

| Run | Decisions / 22 | Binary probes | Wrapper comparisons | Essential strict containments |
|---|---:|---:|---:|---:|
| Original default | 3 | 863 | — | — |
| Original cap 1 | 3 | 863 | — | — |
| Wrapper default | 22 | 3,930 | 37 | 9 |
| Wrapper cap 1 | 18 | 3,822 | 30 | 8 |

The cap-one wrapper returned four state-cap declines. No timeouts, omissions or exhaustive solver fallbacks. Across the cohort the recoder used 13 variable copies per cap setting. Invocation totals in seconds were .031 and .060 for the original, .163 and .190 for the wrapper (default and cap 1 respectively, excluding import). These are descriptive timings. Source verdicts through 13 bits were exhaustively verified; larger narrow controls used explicit satisfying or contradictory pin certificates.

An independent instrumented pass reconstructed each of the 26 accepted shifts across both caps. It tested every frontier assignment for translated inclusion and verified signed raw future clause-set invariance and fixed processed selectors. Eighteen shifts also passed truth evaluation on every assignment to their at-most-13 active future variables. The other eight passed the exact signed clause-set check. The future is the recoded physical bank including any still-pending equality constraints. The corresponding original input witness was checked separately. Witnesses and full counters appear in results.jsonl. Some narrow formulas are renamed copies of a published structural family; those cases test order sensitivity, not a new mathematical family.
