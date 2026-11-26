# Twelve point leaves and nine line leaves at twenty mixed gates

With 20 mixed gates this boundary is a tree. The proof below excludes every bank of nine distinct nonzero line signatures at total size 33. The 19-mixed exclusion needs revisiting in two places: a width-eleven point-bank bound on four private groups and a line-cost-five cutoff in the old no-AND enumeration.

An empty signature allows a mixed gate to be removed after clamping. Duplicate nonempty signatures may be identified after lowering each line wire to the OR of its singleton signature. This changes the width and surplus. A full exclusion for circuits with duplicate signatures also requires the corresponding smaller-width results with twelve point occurrences.

With distinct signatures the 24 missing-singleton banks and the 7,140 ordinary banks exhaust all nine-line possibilities. The missing banks cost three line gates; their line cograph and private-guard analysis provides four disjoint pair-safe groups, independently of point-leaf count. The accompanying width-twelve certificate requires at least twelve paid point gates for these groups. The total is therefore at least 35.

For ordinary banks let c be the exact cost of the two genuine masks. The previous reconstruction cases cost at most P−7+d point gates, where d is the excess for cell repairs or duplicated cofactors. Since seven canonical outputs cost 21 paid point gates in the singleton relaxation and the mixed tree has P+8 gates, the resulting original total is at least 36+c−d. Thus the same threshold d≤c+2 proves total ≥34 at both P=11 and P=12. This transfer requires that the original certificate bound d without a width-eleven point-bank assumption.

* Full-good banks have d≤4, by disjoint guards and the min(e,8−e) bound for a joint two-cofactor block with e point occurrences. This is independent of P. Their minimum c is two.
* For punctured banks with no raw-splitting AND, the placement tests bound d solely through pivotal repairs, laminar resident sets, the local size e of a duplicated block, and unused point occurrences. No global P limit is needed by the final checks in ../double-clamp/no-and.md. In the small-block refinement e≤4 is enumerated and e≥5 is handled by direct construction. The older Python maximum over 0≤e≤11 of min(e,8−e−r) is already global for nonnegative repair count r, since the second argument decreases beyond four. The inherited placement summaries cover c≤5 only.
* For one missing split edge and for two disjoint missing split edges, ../ordinary-line-nine/exceptional.md and finish-single-edge.md bound the same d through disjoint opposite-child computations, marked-point tests and compartment inequalities. The compartment model allows arbitrary monotone maps in its regions. Its operative parameter is the excess, not the global number of point leaves.
* In the adjacent cost-two cases, the opposite-child PAIR and TRIPLE arguments have either d≤4, or four disjoint pair-safe groups of original point leaves. The joint placements needing four private groups cannot cite the old P11 point checker here. The new twelve-slot checker gives 20+2+12≥34 for precisely those placements. For the remaining disjoint-expression cases use d≤4 directly, so P=12 increases the recovery cost by one while decreasing the available original point budget by one.

The following counts, before distinguishing the placement of the raw-splitting AND, are reproduced by linesplits.py. The no-edge column counts punctured banks with a witness for every raw split. In the split-edge columns the no-AND placement must also be tested.

| c | Full-good | No edge | One edge | Two disjoint | Two adjacent |
|---:|---:|---:|---:|---:|---:|
| 2 | 0 | 0 | 105 | 105 | 105 |
| 3 | 254 | 96 | 840 | 0 | 0 |
| 4 | 1,279 | 261 | 735 | 0 | 0 |
| 5 | 1,828 | 174 | 336 | 0 | 0 |
| 6 | 917 | 42 | 63 | 0 | 0 |

The width-12 line budget newly allows c=6. Of its 1,022 banks, 917 are full-good. All other 105 pass the absolute no-AND bound in ../ordinary-line-nine/noand.py. The 63 that could have an exceptional AND also pass the one-edge absolute bound in edge.py. These new checks do not use the old cost-five-cutoff file. Together with the occurrence-linear transfer and the width-twelve four-group result, all 7,164 distinct nine-line banks at P=12 are excluded.
