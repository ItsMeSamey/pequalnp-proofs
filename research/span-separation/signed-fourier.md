# Single-exponential dense terminal test for signed-graph columns

Use the supplied signed-graph representation and pure lift u in even-cycle.md. There is a deterministic 2^k poly(input) algorithm returning a witness for arbitrary dense K and w, where k=dim K.

A separating functional is a vertex coloring. It satisfies d≤k linear equations: at most k−1 from generators of K other than u, and one prescribing its value on w. A compatible coloring supports u exactly when its monochromatic edges contain a negative signed cycle, since an even-degree edge set is a binary sum of cycles. For each possible cycle color c start from the constant c coloring. Write γ_v in F₂^d for vertex v's column in the d parity equations, and b for the residual right hand side. It suffices to find a negative cycle disjoint from a set S of original vertices with sum of γ_v over S equal to b. Flip those vertices to obtain a valid coloring.

Replace each edge by a private length-three path with the same sign product. This makes a simple graph even for loops or parallel edges, and preserves negative cycles. Only original vertices may belong to S. Let A be its unsigned adjacency matrix, Aσ its signed adjacency matrix, and n' its vertex count. Both matrices have zero diagonal. For character index j define D_j diagonal with value 1+(-1)^{j·γ_v} on original vertices and 1 on auxiliary vertices. Test whether the integer polynomial

    P_b(t) = sum_j (-1)^{j·b} (det(D_j+t Aσ) − det(D_j+t A))

is nonzero.

Expand determinants by permutations. A permutation contributing a difference has negative total sign product along its off-diagonal edges. Transpositions have positive sign product. The degree in t counts moved vertices. Expanding the diagonal factors at fixed vertices and summing over j gives 2^d times the number of flip subsets S of fixed original vertices with syndrome b. Consequently every nonzero permutation contribution contains a negative simple cycle disjoint from a valid S. Conversely take a shortest negative cycle disjoint from any valid S. Its cyclic orientations, fixing all other vertices, contribute. At the least degree of any contributing permutation exactly one negative simple cycle is present and every other vertex is fixed: retaining one negative cycle and fixing all other vertices retains the same S. All such minimum-degree terms have common permutation sign (-1)^(length−1) and sign-product difference −2, so they cannot cancel.

Evaluate P_b at n'+1 distinct nonnegative integers with exact determinants. Its degree is at most n' and the integers used have polynomial bit length by Hadamard's inequality, including the additional d bits needed in summation. This proves the claimed decision time. For witness extraction at a successful c, delete original edges while feasibility persists, retaining all original vertices as selectable even if they become isolated. The minimal remaining edge set is a single negative cycle. Solve the terminal equations on vertices outside the cycle by Gaussian elimination and return the cycle's original edge columns as X.

The proof applies to the nonregular Fano-minor examples in even-cycle.md. It makes no assumption of sparse terminal vectors. Two independent reviews checked the sign and cancellation argument, the subdivision step and witness extraction.

An independent [permutation-expansion check](check_permutation.py) compares 400 exact signed determinant values.
