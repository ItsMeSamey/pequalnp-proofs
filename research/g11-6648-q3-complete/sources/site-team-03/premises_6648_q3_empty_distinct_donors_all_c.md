# Empty S and two raw-positive ORs with distinct dirty donors, all c

Assume the original hypotheses of premises_6648_q3_empty_c1_distinct_donors.md (9706324a…), now permitting arbitrary c. Use its original guard aggregation, named-reader dichotomy at exactly one near star and original anchored footprint. The case c=1 is in that file. Let c≥2. All clean roots counted by c directly consume a raw-empty wire. There is no raw-empty OR: the first such wire would directly consume an AND, whereas both physical dirty-reading ORs are raw-positive. Hence each centreless root consumes a direct dirty AND. A common direct pin of two clean tops permits factoring their disjunction and saving a gate. Thus choose c distinct direct dirty predecessors, choosing S for A, so c≤j.

Each donor preceding both exits is a pure product and cannot be S. If so every primitive clause contains y,z, because S is bivalent on those singletons. Its unique possible lambda anchor is x, which has no original star. Only one other paid OR Q exists, forcing every primitive to be the same wire and S redundant. The same argument applies to any donor not depending on an earlier exit. Order donors by occurrence D1,D2.

If S is distinct from both donors, at least d=max(0,c+2−j) of the c−1 non-A roots have a direct donor pin. Without one, each root expands to at most four pure products by the two donor flags. In the nested case use D2=D20∨D1K, D20⇒K, and substitute into four input modes: P00, D1P10, D20P01, D1K P11. This identity permits direct multiplicative occurrences by cutting D1,D2 additionally at those occurrences. The other modes for a root directly requiring a donor shrink to at most two. If it requires D2, the two bases are D20P01 and D1K P11; for D1 they are D1P10 and D1K P11. Each term is below the original clean root. Add at most three ordinary terms as in the c1 proof. On H, which loses A, the resulting count is n≤4(c−1)−2d+3.

If S=D2, globally allocate D2-positive H edges to D20 and D1K. Both are clean on H because D2≤S there and independent H inputs may adjoin x. On D2-negative H pairs, cut D2 to false globally; at most two products per remaining centreless top and one ordinary D1 correction suffice. Hence n≤2c+1. A direct multiplicative D1 factor in D2 is included by taking a zero base. All counts use the same single projected exception Q. The raw supports of the two injectors in zero mode are just their existing raw-positive partners. No transfer of leastness after specialization is required.

With two or more near stars, at most three near residuals remain. With exactly one, at most four remain. If one of the two forced paid individual readers is Q, every H batch is fully anchored, since its raw mode projects to the other input and its active donor modes remove satisfied clauses. If both are the exits, both ordinary opposite guards vanish on H, as proved in the c1 note. This decreases n by two for S-distinct (joint term only) or by one for S=D2 (no D1 correction). Using upper bounds instead of actual mode counts preserves these savings.

For one common binary exception and ≤3 internal H stars, H coverage is at most n+1. With ≤4 it is at most n+2. See premises_6648_q3_empty_repeated_donor.md (5aaae5b7…) for the four-star argument and shared touching-pair restriction. With no exception, ≤3 internal stars give n and ≤4 give at most n+1 by anchored footprints.

| c,j | Target | n upper | Internal stars in a violation, ≥2 near / exactly 1 near |
|---|---:|---:|---|
| 2,3 | 10 | 5 | 3 / 4 |
| 2,4 | 11 | 7 | 2 / 3 |
| 3,3 | 12 | 7 | 1 / 2 |
| 3,4 | 13 | 9 | 0 / 1 |

In the first column of star bounds, n+1+3 meets the target in every row. With one near star and Q a named reader, add four to n, plus one only in the four-star row. With both exits named, subtract the savings above before applying n+1+4 (n+2+4 in the four-star row). In the row (2,3) the S=D2 savings of one leave 4+2+4=10. In (2,4) and (3,4) the larger n arises only for S-distinct; the S=D2 counts before savings are 5 and 7.

For c=2,j≥5 the count n≤7 and any violation would require U≥13, giving ≤2 internal stars and U≤7+1+4=12. For c=3,j≥5 the only possible violation is U=15 at j=5. Then exactly one star exists globally. Four individual OR readers are impossible because at least one is lambda, whose other raw pin contributes a distinct leaf by leastness, producing two distinct original stars. In the common-AND case the sole star is yz, so every ordinary opposite raw guard vanishes on H since each such leaf is incident to an original star. At most one joint ordinary product remains, giving n≤9, also sufficient in the S=D2 variant. There are zero internal stars, so U≤9+1+4=14. For c≥4, j≥c and U≤15 prove the claim.

This extends the frozen c1 proof without additional numerical jobs. It uses the sparse one-exception footprint and original labelled 19/15 card reader classification.
