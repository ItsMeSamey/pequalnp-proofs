# All point-width-12 interfaces at 23 mixed gates

At total size ≤33, exactly 23 mixed gates leave ten pure gates. For point width 12 the necessary point price is at least five. Line separation requires at least seven distinct line wires, and every line input beyond the seven raw lines needs a paid gate. Thus the only line widths are 7 through 12. At line width L the surplus is 12−L.

| L | Primary computation | Independent status at assembly |
|---|---|---|
| 7 | Four shared-guard cases have empty frontiers at gate 9. The five-special branch has 204 point records, 70 banks and 350 bank/label hypotheses. Its uncapped partition census gives 219,444 ordered assignments, 119,814 after exchange symmetry. All 119,814 fail the pivotal exact check. | Source review of fixed roles, pivotal continuation and 204→70→350 passed. All four guard cases independently replayed. A fresh full numerical run is underway. |
| 8 | All extra masks covered. The 14,051 genuine pairs leave 3,231 placement candidates, of which 3,170 are physically admissible and all fail exact synthesis. All 4,279 triples, 757 quartets, 73 quintets, six sextets and 322 singleton-extra placement survivors fail. The zero case folds below 23 mixed gates. | Independent source and 765-point-row audit plus a limited sextet replay. |
| 9 | Point price 5–8. Initial assignment domain has 140,228 relaxed cases. Terminal exact checks reject respectively 0, 384, 2,400 and 57,154 ordered partitions, totaling 59,938. The final 57,154 are checked in a 4,000-row prefix and a 53,154-row suffix with no gap. | Source review passed for the communication cut, fixed-region continuation and final LCA restrictions. Separate full numerical replay pending. |
| 10,11 | True point-price and physical line domains yield 288,795 and 485,382 joint cases. All fail with no search cutoff. | Primary numerical replay. |
| 12 | Both price-five point orbits are UNSAT even granting five unrestricted extra line features. | Primary SAT replay. |

The four primary archives plus the W13L7 virtual-point dependency are hashed in W12-SHA256SUMS. W12L9 includes the prior point domain twelve-eight.zip. Earlier mixed-gate floors and line-width geometry are indexed in synthesis_new/twenty-two-summary. The result covers W12. Other point widths require separate exclusions.
