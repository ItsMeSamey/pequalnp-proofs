# A maximal negative for shared bilinear trace tests

Let q=p^n and use the affine chart of PG(2,q) with a point (x,y) and a nonvertical query (a,b) incident when y=ax+b. A test may project the residual into an arbitrary vector space over the prime field. The following argument uses arbitrary point payloads and one original legal mask of exactly q queries.

## Rigidity of flag-complete bilinear tests

Let B(x,y;a,b) be separately affine-linear over F_p in the two coordinate pairs, valued in an F_p-vector space, and zero on every affine flag. Expand it as

    U(x,a)+V(x,b)+W(y,a)+Z(y,b)+L_x(x)+L_y(y)+L_a(a)+L_b(b)+c,

with bilinear capital-pair terms and linear single-coordinate terms. On the flags x=b=y=0 we get c=L_a=0. At x=0 and y=b, varying a gives W=0 and Z(b,b)+L_y(b)+L_b(b)=0. At a=0 and y=b, varying x gives L_x=V=0. Substituting y=ax+b now gives U(x,a)+Z(ax,b)+L_y(ax)=0 for all x,a,b. Taking b=0 yields U(x,a)=−L_y(ax); since ax ranges over the field, Z vanishes. The earlier identity now gives L_b=−L_y. Thus

    B(x,y;a,b) = L_y(y−ax−b).

This derivation uses the ordinary affine coordinate representation and no assumption on projective rescaling. A feature computed from nonlinear label embeddings or a branch test not itself true on all flags need not have this form.

## One multiplication table inside the original negative

Choose an affine center o=(x₀,y₀) and a nonvertical carrier line l through o of slope a₀. Select every other line through o (q queries), and use its full independent point complement P=l outside o (q points). In this maximum payload, exactly q−1 affine points have form o+t(1,a₀), t≠0. The q−1 nonvertical selected queries have slope a₀+s, s≠0, with intercept determined by o. The residual on this submatrix equals −ts. There are no incidences, but for each nonzero c the equation −ts=c is a perfect matching between its two sets of q−1 labels.

For each rank-deficient Φ of residuals choose any nonzero c in ker Φ. Its projected incidence test includes that matching. In fact each point and each line has exactly |ker Φ|−1 neighbors in the submatrix. Thus all these labels survive any number of alternating endpoint pruning operations that keep a label when every required projected relation has a neighbor among the remaining opposite labels. This holds even if the tested projection varies by endpoint, provided its kernel remains nontrivial. Separate per-projection witnesses need not describe the same flag.

More generally a tree of existentially assigned point and query labels with one rank-deficient projected relation per edge has a solution in this submatrix: fix its root arbitrarily and extend repeatedly along a matching. For a general bipartite witness graph, even cyclic, prescribe the point-side field parameters t_i arbitrarily. At each query vertex j with incident maps Φ_e it suffices that the sum of their ranks is less than n. The restrictions Φ_e(−t_i s_j)=0 then leave at least p^(n−sum ranks)−1 choices of nonzero s_j, independently across j. There is a dual assertion with the roles reversed. Witness reuse is permitted; no claim covers general circuits that combine partial relations in other ways.

For m charts choose l nonvertical affine in all of them and o on l affine in all; such a choice exists if m(q+1)<N and m<q+1. The same original maximal negative applies. Remove from its two shores the one exceptional nonaffine point and the one vertical query of each chart. In a fixed chart this removes at most m−1 additional labels on either shore beyond those already absent from its table. A test whose kernel has size h still gives each common-core label at least h−m neighbors within the common core. If every tested kernel has size greater than m, all endpoint pruning across the charts leaves this entire common core in place.

## Physical sharing of exact projected verdicts

For a projection Φ with B distinct image values form Q(a,d), the OR of all raw query lines of slope a with Φ(b)=d. Building these families costs at most q² OR slots. For each x and each image value c, compute the OR over all slopes a of Q(a,c−Φ(ax)). There are qB outputs with q operands each, so the whole bank costs at most q²+qB(q−1) gates. Every point (x,y) with Φ(y)=c reads the very same physical output, shared among q/B points. Its verdict is exact for the projected equation on every query mask; no limit on occupancy of any slope class is imposed. Combining it with point selectors for a scalar projected test costs O(N). The rank-one fixed-characteristic case costs O(N) per projection. This is genuine sharing of approximate incidence predicates. The maximal-negative result explains why individually faithful cheap projections need not recover original incidence under the full q-line promise.
