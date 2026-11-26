# Terminal traces with a supplied graph cycle space

Consider a binary representation whose ordinary columns have quotient matrix Q modulo an interface W of dimension r. Split the ambient coordinates and write σ for the W-valued linear map on edge vectors supplied by the ordinary column labels. Suppose a graph D on the same labelled ground elements has binary cycle space S containing C=ker Q, and g=dim S−dim C. For fixed r+g one can compute every attainable W trace, with a witness, in deterministic polynomial time.

Compute g binary row vectors τ by extending a basis of the incidence row space of D to a basis of the row space of Q. This is possible because C⊆S, which can itself be checked by row reduction. On S the simultaneous kernel of τ is exactly C. Label each edge of D by the augmented terminal value (τ_e,σ_e) in F₂^g⊕W. Apply the exact graphic-quotient trace algorithm to these labelled edges.

For each subset X, the augmented trace H′ is the image of S∩F₂^X under (τ,σ). Its intersection with {0}⊕W has second coordinate precisely σ(C∩F₂^X), the original trace on X. Consequently projecting these intersections for every augmented trace gives exactly the original catalog, and each augmented witness works directly for the original trace it yields. At most 2^{O((g+r)²)} subspaces need be considered; each graphic trace test is polynomial for fixed g+r. The required graph and its edge identification are part of the hypothesis. The bounded-pattern graphic algorithm invokes disjoint paths with prescribed sums of binary edge labels. [Liu and Yoo](https://people.tamu.edu/~yyoo/stoc25.pdf#page=3)

## Cellularly embedded cographic quotients

Let the ordinary quotient be the cographic matroid of a connected graph G with a supplied cellular embedding in a closed connected surface of Euler genus g. Let D be the geometric dual under the natural edge correspondence. The space C is the primal cut space. Every primal cut has even boundary in D: traversing a face walk changes sides of the cut an even number of times. Both G and D are connected. With v primal vertices, m edges and f faces, their dimensions give

    dim S − dim C = (m−f+1)−(v−1) = 2−(v−m+f) = g.

The argument applies over F₂ on orientable and nonorientable surfaces and allows repeated face incidences, loops and parallel edges. The auxiliary rows record binary homology on even dual edge sets. The result handles arbitrary dense terminal labels in fixed Euler genus and fixed interface dimension. The checker reconstructs dual graphs from orientable rotation systems, including a toroidal embedding of the nonplanar graph K₃,₃, and compares augmented traces against direct primal cut labels on every edge subset. It checks the reduction independently of the general graphic trace solver.
