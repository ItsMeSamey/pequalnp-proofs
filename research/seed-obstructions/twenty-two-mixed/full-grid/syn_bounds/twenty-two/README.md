# Residual budget 33 with exactly 22 mixed gates

With P point and L line boundary inputs the binary cone has k=23−P−L surplus reads. The two pure programs together cost at most eleven gates. The eleven-point projection floor is nine, the twelve-point floor is five, and thirteen or more points may cost zero. The existing width-ten point exclusion applies at this budget. On the line side the seven raw inputs are necessary in aggregate and each additional physical boundary slot costs a gate. Only the thirteen-point eight-line configuration remains. Listed open prices are necessary and do not claim existence.

| P | L | k | Possible paid point cost | Status |
|---:|---:|---:|---:|---|
| 11 | 7 | 5 | — | Excluded: all seven final geometries have a hard ten-input unrestricted minor |
| 11 | 8 | 4 | — | Excluded by all 83 price-nine and all 317 price-ten genuine frontiers, with the degenerate line cases transferred |
| 11 | 9 | 3 | — | Excluded: 714 joint representatives reduce to 37, and all 37 fail the exact mixed frontier |
| 11 | ≥10 | ≤2 | — | Pure budget |
| 12 | 7 | 4 | — | All prices excluded, including the b=9 case; see twelve-seven-four.zip |
| 12 | 8 | 3 | — | Excluded at all prices; 42,918 price-nine representatives reduce to nine and all fail, and 274,556 price-ten pair cases fail |
| 12 | 9 | 2 | — | Excluded by syn_verify/twenty-two-nine-point-nine and lower-price two-cut replay |
| 12 | 10 | 1 | — | Excluded at all prices by syn_verify/twenty-two-ten-line |
| 12 | 11 | 0 | — | Excluded by verification agent’s ordinary and missing-raw LCA checks |
| 13 | 7 | 3 | — | Seven-line three-surplus theorem |
| 13 | 8 | 2 | 7–9 | Prices through six and price ten excluded; any remaining genuine extra has 2–5 labels |
| 13 | 9 | 1 | — | All prices excluded. Final price-nine pentad closed all 1,660 exact frontier cases in W13L9-nine-complete.zip. |
| 13 | 10 | 0 | — | Excluded by 191,005,260,830 private-LCA bank comparisons |
| 14 | 7,8,9 | 2,1,0 | — | All excluded |
| 15 | 7,8 | 1,0 | — | All excluded |
| 16 | 7 | 0 | — | Excluded |

There is no higher P (L≥7). A feasible seven-line bank always has the raw singleton signatures. The seven-line k≤3 structural result applies at all widths under total cap 33; for k=3 its exact hypothesis P+g≤24 follows from the mixed count P+9. Eight-line k≤1 is also excluded at all widths and admissible line costs. At P14/L9, all generic read-once nine-line shapes were already excluded independently of P. The adjacent-pair and missing-singleton residues require four disjoint pair-safe ordinary groups, so diagonal_fourgroups requires g≥24−14=10. With line cost at least two only nine point gates remain. Zero and duplicate signatures route to the seven- or eight-line theorem after simplification.

At L8 every multiset contains all seven raw singleton signatures plus one arbitrary seven-bit signature E, by the raw line obligation basis classification. Cost c≥1 is mandatory even when E is zero or duplicates one existing singleton. If |E|≥2, its minimum singleton-domain price equals |E|−1, attained by an OR tree. With P11 and g=9 this permits 64 eighth masks (zero, singletons, pairs and triples); at g=10 there are 29 (zero, singletons, pairs). At P13/L8, a zero or duplicate extra collapses to a seven-line circuit with at most three surplus reads. At point prices seven, eight, nine, and ten the line gate budget is respectively four, three, two, and one. A genuine extra can therefore have at most five, four, three, or two labels, respectively.

At P12/L11 the 461 cost≤7 point banks have counts 5, 53 and 403 at prices five, six and seven. The corresponding line budgets are six, five and four. The ordinary seven-raw-plus-four-extra cases all fail the LCA test. Missing a raw line costs at least five because the eleven boundary slots then require at least five new signals. All seven feasible missing-raw point orbits at point price five or six also fail. The physical cell is closed in syn_verify/twenty-two-eleven-line.

At P13/L10 point cost eight requires exactly three line gates, giving 8,275 possible multisets. Point cost seven or below was tested against all 361,245 covering ten-line multisets. The private-LCA checker in syn_cover/thirteen_ten excludes both sets of allocations.

The full ten-line cover census now has pure singleton-domain prices three through eight. Among 357,760 ordinary raw-seven-plus-three-extra banks the exact counts are 8,275; 37,415; 89,915; 121,051; 82,859; 18,245 respectively. The 3,485 other multisets contribute zero at price three and 960; 1,308; 881; 288; 48 at prices four through eight. Source and replay: syn_cover/thirteen_ten/prices.py.

The W13/L10 private-LCA check has completed. At point budget seven, all 466,589 point representatives fail against all 361,245 line multisets; at point budget eight, 2,713,271 point representatives fail against the 8,275 affordable line multisets. This covers all 191,005,260,830 comparisons.

For W11 minimum-price frontier checks, minimum11.py derives the domains from the preceding point equality certificate. At L=7,8,9 it generates the complete and genuine-only input banks (g7.in, g8.in and g9.in). The latter omit repeated and zero line signatures. See minimum11-proof.md for the transfer from the omitted cases and the justification of the gate-parent dominance filter. Build parents22.cpp with a C++17 compiler and pass the selected bank input on standard input. A nonzero exit status reports a surviving final state or failed input validation.

## Nine-line read-once planes at larger mixed totals

For any total-size-33 circuit with nine line slots and no surplus, m=P+8 and line cost is at least two. Thus g≤23−P. The adjacent-pair and missing-raw cases force four disjoint private groups. The width-independent proof in four-private-uniform.zip establishes g≥11, excluding every P≥13. The former width-specific diagonal certificates give independent checks at P=13–17. Lower widths use the through-twenty exclusions. Generic read-once line families use the width-independent reconstruction; zero and duplicate signatures collapse to seven or eight distinct inputs at already excluded surpluses. This covers every feasible nine-line read-once width.

The independent unmarked W11/L7 nine-paid frontier exhausted two of its three point geometries. Its third replay was retired after the structural proof at syn_mitm/w11-seven-five verified the entire nine- and ten-paid domains. The structural proof supplies the full lower bound in the table.
