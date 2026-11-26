# Deleting one column restores binary representability

Consider the GF(16) weak-map comparison for equality-spanning with two independent binary pin vectors. A physical M-basis failing in N solves the problem. Suppose some index e has full-rank connected M without e and binary N without e. Try every e if unspecified. Choose a clean M-basis. If it already solves the pins return it. Otherwise in its normalized coordinates

    N_j = A_j + w g_j / p

where A_j is binary, p≠0 is the pinned discrepancy, g_j belongs to GF(4) and measures the label discrepancy from basis interpolation, and w=p1+λ p2 for the binary pin columns p1,p2 with λ outside GF(4). The entries of w have at least two distinct nonzero types among 1,λ,1+λ because the pins are independent. Basis gains are zero.

Diagonal scalability recognizes binary N on the clean normalized representation. Run the established binary weak-map comparison on the clean restriction to find any differing basis. If none, normalized supports coincide there. A missing M-nonzero would allow a single exchange; an additional N-only arc closes a directed alternating cycle in the connected clean fundamental graph. A shortest such cycle gives a differing basis, as its induced support has one M matching and two scalable N matchings.

If all clean gains vanish, invoke the one-gain algorithm on the shifted problem. Otherwise every nonzero-gain clean column must have ones in M on every row of S={i:w_i≠0}, by support equality. Fix two such rows of different types x,y. Scalability requires (p+xg)/(p+yg) to be equal for all nonzero clean column gains g. No denominator vanishes on the shared support. Cross multiplication yields p(x+y)(g+g')=0, so they all equal a single g0.

Normalize the diagonal scaling so one gain-g0 column has column factor 1. Then the row factor on each type x in S is s_x=p/(p+xg0). These factors are distinct and different from 1. Every gain-g0 column has the same column factor 1 by any entry in S; each of its occupied outside rows has row factor 1. Zero-gain columns connect only rows of equal factor. By connectedness all row factors lie in {1} union {s_x}. Rows outside S may belong to any of these groups.

Write V0 for factor-1 coordinates, V_x for factor-s_x coordinates, t for the indicator of S, and t_x for its portion in V_x. Each gain-g0 column in M is t+v_j with v_j in V0. All zero-gain columns are local to one group. The scaled clean N representation agrees with clean M, including separately rescaled basis columns. Let a be the binary rogue column and let a0,a_x be its row-group portions. Its GF(16) value after the clean row scaling, with no further rogue column scaling, has portions

    a0 in V0;     s_x (a_x + x g_e t_x / p) in V_x.

The four binary slices and a are thus in K=span(a0, all a_x,t_x), of dimension at most seven. Make one block for the local clean columns in each V_x. Make a final block for all V0-local columns and all t+v_j columns. Each sector block meets K in at most span(a_x,t_x). The final block lies in V0 plus span(t), so meets K in at most span(a0,t). The ordinary block spans are jointly independent modulo K since t∈K and all remaining block coordinates lie in distinct coordinate sectors modulo their local K terms.

Compute each block's attainable traces on its actual intersection with K, of dimension at most two, with physical witnesses. By private independence a selection's trace on K is exactly the sum of local traces. Combine the bounded tables and ask whether a span contains every binary slice of the rogue N column and avoids a. If so, enlarge the chosen clean span to rank r−1 while avoiding a by adding clean columns with independent projections modulo a. Full ambient clean rank ensures this can reach r−1. Including e then gives a physical M-basis dependent in N. Every differing basis using e conversely yields such a trace. This is a polynomial full-target solver under the clean deletion and connectivity assumptions. No slice-rank bound on e is required.
