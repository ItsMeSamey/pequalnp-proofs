# A count-preserving reduction modulo three through simple cubic independent sets

Given a 3-CNF formula φ with its declared variable list, the following polynomial-time map produces a simple cubic graph G with

    #IS(G) = #SAT(φ)  (mod 3).

It also produces a signed CNF with three distinct literals in each clause, each raw variable occurring once positively and once negatively, whose canonical multilinear extension at the all-2 point of F₃ equals this residue. These are residue equalities for every input, including satisfiable formulas whose model count is divisible by three.

## From assignments to a weighted independent-set count

Use R = [[1,1],[1,0]], with states 0 and 1 for empty and occupied. For each declared variable, introduce two vertices of activity +1 for its positive and negative literals. Join them and add a common neighbor of activity −1. When both literal vertices are empty, the neighbor sums to 1−1=0. When exactly one is occupied, the neighbor is forced empty and contributes 1. Both occupied is forbidden. For each clause add an activity −1 vertex adjacent to each distinct literal in that clause. Summing it gives zero on a false clause and one on a true clause. All auxiliary vertices are independent conditional on the literals. This signed partition function over the integers equals #SAT(φ), including the factor of two for each unused declared variable.

## From arbitrary degrees and signs to unweighted degree at most three

Replace a degree-d vertex by a chain of d incidence copies between two terminals. Attach each original edge at its own incidence copy. Every chain link is a path of six hard-core edges, with the five intervening activities −1,−1,+1,−1,−1 in that order. With D = diag(1,−1), multiplying the two-state matrices gives R D R D R = diag(−1,1). Two such half-paths joined at an activity-one midpoint have identity interaction. The chain only contributes when all its copies agree. Put the original activity at one terminal and give the remaining copies and terminal activity +1. All degree-three copies now have activity +1, and every negative vertex has degree at most two. This also works at d=0. The equality construction follows the existing [positive read-twice projection note](../pnp-general-separation/read-twice-positive-cnf-projection.md).

Give each negative vertex unit activity and attach one fresh unit leaf. The two conditional contributions at this vertex are now (2,1), congruent modulo three to 2(1,−1). If the number of such leaves is odd, add one isolated vertex with count 2. The total scaling factor is then one modulo three. The graph is simple, unweighted and subcubic.

## Filling degree vacancies exactly modulo three

For a rooted fragment with root degree two and all other vertices of degree three, write (P,Q) for its total independent-set count and its count with root absent, reduced modulo three. Adjoining its root to an external vertex contributes P when that vertex is empty and Q when it is occupied.

| Fragment | Root absent, as an integer | Root present, as an integer | (P,Q) modulo three |
|---|---:|---:|---|
| A, subdivide an edge in K₃,₃ | 16 | 7 | (2,1) |
| B, subdivide a matching edge between the two triangles of a triangular prism | 14 | 7 | (0,2) |

The subdivision vertex is the root. For A, deleting the subdivided edge from K₃,₃ adds its endpoint pair to the 15 independent sets. Occupying the root leaves K₂,₂. For B, the root-absent graph has 1 empty set, 6 singletons and 7 pairs drawn from opposite triangles. Occupying the root leaves a four-cycle.

Join fresh copies of two fragments U,V under a new root adjacent to both old roots. The resulting signature is (PᵤPᵥ + QᵤQᵥ, PᵤPᵥ). Thus C = A * B has signature (2,0), and D = A * C has signature (1,1). D has 23 vertices. Attach one disjoint copy of D for each missing degree at every external vertex. The result G is simple and cubic, and its count retains the original residue. Each construction has linear size in the incoming graph plus its incidences.

## Opposite signs in the target CNF

Give each vertex one clause. Orient every edge arbitrarily and give it one raw variable occurring positively at its tail and negatively at its head. For the multilinear extension at raw success parameter 2, a single raw bit has weights −1 on both Boolean assignments. In the clause inclusion–exclusion expansion, a selected endpoint asks that its literal be false. Summing the raw bit gives 1 for no selected endpoint, −1 for one, and 0 for both. Its matrix is

    [[1,−1],[−1,0]] = D R D.

Only independent sets S of selected clauses contribute. Their inclusion–exclusion sign is (−1)^|S| and the edge factors supply (−1)^(3|S|). The product is one. The all-2 evaluation is therefore #IS(G) modulo three, with no global normalization.

For an ordinary Boolean model-count target, m raw variables instead give evaluation = (−1)^m #SAT(target) modulo three. If m is odd, append the clause construction for a disjoint K₄. This adds six variables and multiplies the evaluation by five, congruent to −1. The resulting Boolean target count agrees with #SAT(φ) modulo three in both parity cases.

The reduction preserves counts modulo three. Auxiliary assignments need not correspond bijectively over the integers.
