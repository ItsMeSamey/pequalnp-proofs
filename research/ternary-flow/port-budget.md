# Fixed ternary charges with private local auxiliary variables

Let each edge e have a public block of m_e Boolean coordinates, with three distinct words denoting its F3 symbol. Vertex guards use only their incident public blocks and arbitrarily many private coordinates. All private coordinates and row allocations are disjoint between gadgets. Each private coordinate provides at most one native pivot; each public coordinate can provide at most one globally, and one extra terminal clause is available. Let r_v count rows of a gadget not accounted for by its own private pivots. For every accepted public point there is an accepting affine flat of public codimension at most r_v through that point. This applies even with cyclic private dependencies, by the affine chart theorem, and remains true on restriction to an affine subspace through the point. See audit/private-budget.md for a proof using a minimum-support witness.

Allow edge-domain validation in two ways. An independent edge gadget may accept precisely the three words on e. Alternatively assign e to an endpoint which, as part of its full local predicate, rejects a malformed owned block whenever the unowned incident blocks are legal. On fully legal words the star predicate is precisely the required signed ternary charge. The edge and vertex gadgets may be different at every location, and all vertex charges are fixed.

An independent edge validator needs at least m_e−1 nonprivate rows because the three words contain no affine plane. At any star fix a valid tuple. Keep the entire public block for each owned edge; for each unowned edge restrict to a line consisting of its value in that tuple and a different valid word. This gives an ambient binary affine space of dimension d+sum_owned(m_e−1), where d is the star degree. Consider an accepting affine flat through the chosen tuple on this space, of dimension k, parametrized injectively by y in F2^k. Since unowned blocks remain legal throughout and the star validates owned blocks, the projection to each block is an affine flat of at most three words, hence a point or a two-word line. A varying edge symbol therefore has the form s_e+delta_e l_e(y) in F3, with delta_e nonzero and l_e a nonzero binary linear form taking values 0 or 1. Absorb its incidence sign into delta_e. The charge requires sum_e delta_e l_e(y) to vanish identically. Writing l=(1−(-1)^l)/2 over F3 and using character independence, the sum of the nonzero delta_e values in every class with the same l must vanish. Every such class uses at least two edges. The l span dimension k because the parameterization is injective. Consequently k<=floor(d/2).

The star thus needs ceil(d/2)+sum_owned(m_e−1) nonprivate rows. Summing over vertices and independent validators gives a total demand of at least

    sum_e m_e + (number of odd-degree vertices)/2.

This exceeds the available sum_e m_e+1 whenever more than two vertices have odd degree. In particular arbitrary hardwired-charge cubic families with four or more vertices cannot have this modular exact representation, even using unbounded private auxiliary sets and nonuniform bit encodings.

When all domains are enforced separately, choose every alternative symbol so its SIGNED change is +1. On the product of these d lines a star accepts exactly toggles of weight zero modulo three. Over F3 each nonzero l in the preceding argument must then occur a multiple of three times. Hence k<=floor(d/3) and the demand is at least

    sum_e (m_e−1) + sum_v (d_v−floor(d_v/3))
    >= sum_e m_e + |E|/3.

This bound applies even to even-valent graphs. A fixed number of entirely exceptional bounded-degree local gadgets can be omitted with only a constant reduction in demand. A global encoding that admits malformed local words, has overlapping private scopes, or accepts a strict subset of the legal stars can escape the specified hypotheses.
