# Minimum-area 17-covers can repeat entries only on a partial permutation

Use the row-scaled rank inequality and the secant s=17125/93899, b=3030/93899 from anchored-rank.md. Write W=Z+E for the multiplicity of a putative 17-cover, with nonnegative integer E. When the area is exactly 847, the sum of all entries of E is 72. For each row of excess e and squared multiplicity sum Q, its true rank cost f=(25+e)²/[125Q−4(25+e)²] satisfies f≥1−se−b. Summing all nonnegative row gaps f−1+se+b gives at most 72s+31b−14 = 12344/93899 < 0.132.

Every row has e≤4. The coarse gap se+b−D(e) from anchored-rank.md already exceeds 0.17 at e=5 and increases for e≥5. For example D'(e)=120(1250e+50e²)/(625+50e+121e²)², which is decreasing beyond 5 and below s there. If e=2,3,4 and the excess is in more than one column, the squared excess is at most (e−1)²+1. Substituting the corresponding upper bound Q≤25+2e+(e−1)²+1 into the individual gap gives at least 60750/386477, 12250/79453, 33985000/188830889 respectively. Every value exceeds the entire available gap. The cases e=0,1 are immediate.

Thus in each row the excess occupies at most one cell and is at most four there. The transpose gives the same statement in each column. In particular every two selected rectangles intersect in at most one cell: two cells of a rectangle intersection would include a pair in the same row or a pair in the same column.

Furthermore at least fourteen entries of E are ≥3. For real x in the kernel of W, ||E x||²=||Z x||²=5||x||²+20(Σ x_j)². If fewer than fourteen columns have weight ≥3, the nullspace of dimension at least fourteen contains a nonzero x vanishing on all those columns. Since E is a weighted partial permutation, ||E x||≤2||x||, which is impossible.

At a 4×13 anchor accompanied by exactly five further area-at-least-48 rectangles, the maximal possible area is 52+5·60+11·45=847. All above conditions apply. Each of the eleven area-45 shapes can be 3×15, 5×9, or the transpose of either. The conditions do not yet exclude this case.
