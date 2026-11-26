# A wide negative-rank chain with no dispensable gate

Choose m disjoint incidence flags as a seed matching. For each of m new distinct points x_i choose two distinct incident lines a_i,b_i, all 2m line variables distinct and disjoint from the seed endpoints. To take m=q in any plane of order q≥3, place all stage points on a line L and choose two centers c,d off L. Omit the point where cd meets L. For each of the remaining q points x_i use a_i=cx_i and b_i=dx_i. These 2q lines are distinct since the only line joining the two centers meets L at the omitted point. Choose the seed afterwards from a perfect incidence matching, discarding all edges touching the 3q stage endpoints. At least N−3q≥q edges remain for q≥3.

Let F₀ be the OR of the seed conjunctions. For i from 1 to m compute five gates:

    R_i = F_(i−1) OR x_i
    B_i = F_(i−1) OR a_i
    C_i = R_i AND B_i
    D_i = R_i AND b_i
    F_i = C_i OR D_i

Distributivity gives F_i=F_(i−1) OR [x_i AND (a_i OR b_i)]. The output computes precisely the seed flags and the 2m new flags. Every prior-stage F and every R has two outgoing occurrences; the other internal wires have one, apart from the output. All 5m raw variables are read exactly once. There are 7m−1 gates. For the nested independent point-only masks X_j={x_1,…,x_j}, R_i(X_j)=1 exactly when i≤j. Their evaluation matrix has rank m over every field. Each R_i has minimum zero-certificate size at least m+1, since killing it means killing its own x_i and hitting every seed edge.

All operand forwardings at the stage gates change the function. At R_i, retaining only x_i loses a seed flag; retaining only F_(i−1) loses (x_i,a_i). At B_i, retaining only a_i loses a seed flag, and retaining only F_(i−1) loses (x_i,a_i). Forwarding C_i to R_i accepts x_i alone, and forwarding it to B_i accepts a_i alone. Forwarding D_i to R_i accepts x_i alone, and forwarding it to b_i accepts b_i alone. At F_i either forwarding loses one of the two new flags. Private flags cannot be recovered by later stages since none of their fresh points is active. A false positive cannot be undone since each later accumulator dominates its predecessor. The seed matching OR and its individual edge ANDs are likewise irredundant. A global distributive rewrite of the whole stage is possible; operand irredundancy does not imply size minimality.

For an exact incidence embedding, OR the chain with an ordinary star formula for all plane flags except the seed and 2m stage flags. Missing terms can simply be left out of the corresponding star disjunctions. The same positive witnesses still distinguish every downward stage edit and pure singletons still distinguish every upward stage edit. Internal fanout remains at most two. The stated 5m raw uses belong to the chain, while the residual formula reads many additional variables. This exhibits an additive-cost obstruction at the level of a subcircuit; it gives no near-linear circuit for the entire incidence predicate.
