# Counting on the occurrence-one matching class

Take a simple graph G with v vertices and m edges. Remove isolates first and multiply the recovered independent-set count by 2 per isolate (empty remainder is trivial). Choose t=v+1 and make 2t fresh physical K2 shells per edge uv. For each shell allocate fresh endpoint colors (p_u,p_v),(q_u,q_v). Each original vertex cyclically orders its incidence copies; equate each incidence's q to the next incidence's p. Every physical bit occurs exactly once in an unsigned equality pin. Size is 8tm raw bits plus polynomial wiring. The graph on physical color sites is a matching.

A correction z=1−(p XOR q) on each incidence is allowed per shell in patterns (0,0),(1,0),(0,1). Every original vertex has even incidence degree. Its cycle closes iff the xor of its corrections is zero; every such global choice lifts to exactly 2^v physical words, one initial bit per nonempty cycle. This factor cancels the denominator in the binary-character projector for even vertex parity. Therefore

    #raw = sum over s in {−1,1}^V of product over uv in E of (1+s_u+s_v)^(2t)
         = sum over subsets S of V of 9^(t times the number of edges within S).

The sign choices both positive give base 3, mixed give 1, both negative give −1; the even power removes the last sign. Reduction modulo 9^t thus gives exactly #IndependentSets(G), since 9^t>2^v. This uses one count query and polynomial-time integer postprocessing. It is a metric counting reduction, not a parsimonious reduction. Exact raw counting is #P-hard; membership follows by guessing all physical bits. A count modulo 2^p with p supplied suffices by taking p=8tm+1, recovering the full integer. No fixed-precision hardness claim follows.

All constructed instances admit z=0, so they are YES for decision. More generally decision and witness are polynomial on the entire occurrence-one class by the cactus/matching algorithm. The difficulty of counting this class cannot be used as a decision lower bound.

### Binary precision changes the clock

For signed or unsigned occurrence-one copies with no unary pins, contract the consistent copy links as in cactus-copy.md. Every comparison-graph class contains at most two physical bits, so has degree at most two, counting loops twice. With c connected components and r independent cycles, r≤c. Every realizable correction has exactly 2^c raw lifts by independent initial bits on the components. If c≥p the unweighted answer modulo 2^p is zero (not necessarily infeasible). Otherwise give every comparison its column in the r binary cycle checks. For each shell, add the contributions from the three zero-correction patterns to their new XOR syndromes modulo 2^{p-c}. Read the target determined by the all-ones comparison word and signed offsets, then multiply by 2^c. Equal-column choices are counted separately. Time is O(number of shells times 2^r times polynomial(p,index bits)) plus graph setup, and in the nontrivial branch 2^r≤2^{p-1}. This gives fixed-precision and logarithmic-precision tractability, compatible with the growing-precision hardness above. Open or unary-pinned components can lose the free lift factor; the same bound is not asserted for those fibers.

For arbitrary signed copy incidence the same gauge factor and r-dimensional cycle DP remain valid, without r≤c. With excess e=max(0,r−c), the nontrivial branch instead has at most 2^{p−1+e} syndrome states. All parameters are Gaussian/graph computable from the supplied physical system. This estimates the original unweighted residue, not a general signed weighted fiber.

For the counting source, complementing a vertex subset gives a bijection between vertex covers and independent sets; counting vertex covers is already #P-complete on bipartite graphs. [Provan and Ball](https://doi.org/10.1137/0212053).
