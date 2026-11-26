# A connected 3-CNF separation of unbounded treewidth

Let G be the r-by-r square grid with its black/white bipartition, r≥2. Use a selector s, one variable x_v per vertex, and one variable z_e per edge. For e=bw with b black and w white add the two clauses

    (s OR x_b OR z_e),     (NOT s OR x_w OR z_e).

There are 2|E| distinct width-three clauses, with no repeated variables, no tautologies, and no subsumption. The primal graph is connected. Removing s leaves exactly the once-subdivided grid. Contracting one half of each subdivided edge gives the original grid as a minor. Its treewidth is at least r-1: the connected unions of one whole row and one whole column pairwise intersect, and any vertex set of size below r misses some row and some column. This bramble has order at least r, yielding the stated bound. Alternatively, in every tree decomposition the bags meeting each cross form a subtree; these subtrees pairwise intersect and therefore share a bag, which must hit every cross.

Conditioning s=0 keeps only black-centered clauses. For each black vertex b the clauses form a component on x_b and the at most four z_e at b. Each edge has one black endpoint, so these components are disjoint. All white x variables are free. The s=1 branch is symmetric. Each component has at most four clauses and at most five variables. Its degree-four certificate follows from inclusion-exclusion, and its count is 2^deg(v)+1: setting x_v=1 permits all incident edge assignments, and x_v=0 requires all incident z_e=1. Thus the exact count is

    2^|W| product_{b in B}(2^deg(b)+1)
      + 2^|B| product_{w in W}(2^deg(w)+1).

One can find a selector by scanning all variables and testing whether both branches decompose into components of at most five variables. Thus there is a polynomial-time recognition and counting algorithm for the entire class satisfying this structural promise, even if s is not supplied.

The pointwise violation degree on the given unconditioned clauses grows quadratically in r. Set s=0 and all black x_b=0. All white-centered clause violation bits are zero, while the black-centered bits are precisely 1-z_e, one independent bit for every edge e. The indicator of any violated clause then restricts to the full-cube OR on |E|=2r(r-1) bits, of unique multilinear degree |E|. Substituting constants into a putative global certificate cannot increase its degree. Consequently direct global fixed-degree and direct connected-component fixed-degree tests both fail for large r. Direct bounded-component and bounded-primal-treewidth criteria also fail, even though one conditioning step gives bounded components of degree at most four. This is a separation among the stated tests, not an all-algorithms lower bound.
