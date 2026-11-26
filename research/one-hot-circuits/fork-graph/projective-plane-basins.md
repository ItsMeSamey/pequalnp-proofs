# The minimum number of branching wires for projective-plane incidence is asymptotic to one shore

Let N=q²+q+1 and let a single-output binary monotone AND/OR circuit recognize incidence between the one active point flag and one active line flag of a finite projective plane of order q≥2. A branching wire has at least two outgoing physical operand occurrences and may be raw or computed. If h is the number of these wires and g is the size, then

    N(1−(3√q+4)/(q+1)) ≤ h,
    3N−1−N(3√q+4)/(q+1) ≤ g.

These bounds apply to any such plane; the limit is taken along existing orders. The row-by-row disjunction of (point AND OR of its incident lines), implemented by separate binary trees, has exactly N branching wires, all of them line flags. Thus the minimum branching-wire count divided by N tends to one. The construction makes no matching assertion about total gate size.

## Properties of the ordered circuit groups

Use the first-branch partition from branching-packing.md (SHA256 3f3b5e297ca48850a2016ac9f92ecafba9a94ee379d3112d076cc0b2a2de1953), with the no-branch group last. Single flags are cold since every vertex has a nonneighbor. The point–line graph within any one group is a disjoint union of bicliques, each a star since this graph has no C4. Thus the within-group graph is a forest. Between the points of any group and all later lines the edges form a single biclique. In particular, at most one point in that group has at least two neighbors in any fixed later set of lines: two such points would have the same two neighbors. The statement with points and lines interchanged holds as well.

## Incidence estimates

Write M for the N by N point–line incidence matrix. Its row and column sums are q+1, and MᵀM=MMᵀ=qI+J because two distinct lines (or points) have exactly one common neighbor. On vectors orthogonal to the all-ones vector its Euclidean operator norm is √q. Centering the two indicator vectors gives, for any a points and b lines,

    e ≥ (q+1)ab/N − √(qab).

Put δ=N(√q+2)/(q+1). If both a,b≥δ, the right side is at least 2ab/δ≥a+b: divide by ab, use √(ab)≥δ and 1/a+1/b≤2/δ. Hence no group can have both sizes ≥δ, since its forest has at most a+b−1 edges.

Let s=N(√q+1)/(q+1). For any t≥s lines the vector of individual point-degrees has mean μ=(q+1)t/N. The sum of its squared deviations is exactly q t(1−t/N), by the matrix identity on the centered line indicator. Thus the number of points with at most one neighbor is at most q t/(μ−1)². The right side decreases as a function of t when μ>1, and at t=s it equals s. The same bound applies with the shores swapped.

## Locating a cut

Consider the first cut immediately after a group for which at least one remaining shore has fewer than s vertices. Initially both shores have N≥s and ultimately they vanish. If the other remaining shore still has at least s vertices, use this cut. If both now have fewer than s vertices, use the cut immediately before that group. Both shores then had at least s vertices. At least one had fewer than s+δ because at least one shore of the removed group had size below δ. In both cases the chosen cut has one remaining shore of size at most s+δ and an opposite remaining shore of size at least s. The labels of the two shores may be exchanged.

There are at least N−s−δ earlier vertices on the first shore. At most s of them have fewer than two neighbors in the fixed opposite suffix. Every other such vertex belongs to a different branching group by the single-biclique property. The terminal no-branch group cannot precede this nonempty suffix. Consequently h≥N−2s−δ, as stated. The constants are real thresholds and no integer rounding is needed for the inequality.

Every one of the 2N flags must be read, since omitting one would accept an incident edge on its opposite singleton alone. For a live binary circuit the total excess fanout is g−2N+1 and is at least h. This proves the stated size inequality. The separate finite bound h≥ceil((q²+1)/2) in projective-star-deletion.md can be stronger at small q.
