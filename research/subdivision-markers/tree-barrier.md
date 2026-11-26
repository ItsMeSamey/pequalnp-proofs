# Sharp degree obstruction for native acyclic guarded generators

Use a complete binary tree of edge-height h, with one optional bit for each node and an unrestricted root. For every parent bit p with children a,b put the guards

    a=1 implies p=1,
    b=1 implies p+a=1.

They are affine single-alternative guards in acyclic order with at most two predecessor bits per guard. A state bit is read at most three times: in both child guards and, for a left child, in its sibling's guard. When p=0 the first rule forces a=0 and the second then forces b=0. When p=1 either child can be selected and both cannot. Consequently the feasible states are exactly the empty assignment and the indicators of root-to-node paths. There are exactly 2^(h+1) states.

For each vertex v the homogeneous affine marker x_v+x_left+x_right=1 singles out the path stopping at v, treating missing child bits as zero. The marker 1+x_root=1 singles out the empty state. Thus all feasible assignments are individually exposed by one affine marker at a time.

Suppose a sound polynomial map from an arbitrary-dimensional binary cube hits all those one-marker queries and has maximum Boolean multilinear coordinate degree d. Composing a marker with the map retains degree at most d. A nonzero Boolean polynomial of degree at most d takes value one on at least a fraction 2^(−d) of its input cube: a highest-degree monomial remains nonzero on its support variables for every assignment outside them. These singleton-output events are pairwise disjoint, hence 2^(h+1) 2^(−d)≤1, giving d≥h+1. The bound is attained: choose any bijection from h+1 bits to the path states, whose coordinate polynomials automatically have degree ≤h+1. Using only the homogeneous markers exposes all but the empty path, which still gives the same integral degree bound for h≥1.

For k disjoint trees, even imposing just one positive leaf-name unit marker per tree gives m^k disjoint nonempty events for m=2^h leaves. Any shared list of individual assignments answering all such marker queries needs at least m^k entries. If L sound maps from binary cubes (possibly of different dimensions), each of coordinate degree at most d, collectively hit these queries, then each hit tuple in a given map has preimage density at least 2^(−kd), by taking the product of its k leaf coordinates. Hence L 2^(kd)≥m^k. In particular for any absolute fixed d, a marker-independent library of size f(k) times an n-polynomial with exponent independent of k cannot suffice for all these sparse instances. The lower bounds are for shared representations; individual marker queries on this family are straightforward.
