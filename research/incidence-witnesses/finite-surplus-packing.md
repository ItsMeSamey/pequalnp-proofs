# Physical count for packing 12-site restrictions

Write k for the number of retained punctured-Fano graph restrictions and assume the proposed individual lower bound of 21 on the required tests. Every endpoint has the 21-gate star upper bound irrespective of this assumption. The physical baseline on n retained vertices is 2n−4 when the surrounding two-per-raw deletion argument applies.

If the endpoints are vertex-disjoint and there are no cross edges, their union has a circuit of size at most 21k+(k−1)=22k−1. At k≥2 this is smaller than the physical baseline 24k−4. Thus even exact local lower bounds cannot compound the separate +1's there. Such an induced disconnected graph cannot inherit an independent proof of the connected baseline on the union.

If h raw vertices are common to all endpoints and there are no other vertex intersections, n=12k−h(k−1). Fix a single physical circuit on their union. Let t(g) count the local restrictions in which physical slot g survives constant propagation, wire bypasses and dead pruning. No such operation adds slots, and each resulting circuit has at least 21 slots under the hypothesis. Hence
     
     s ≥ 21k − Σ_g max(0,t(g)−1) + |{g:t(g)=0}|.

Consequently the local lower bounds certify 2n−4+k if the overcount minus the count of unused slots is at most (2h−4)(k−1). This is a sufficient condition measured on the same circuit. In particular at h=6 the permitted net overlap is 8(k−1). In the six-common-pole construction, the star O AND (L OR Y0 OR Y1) can be shared physically by every local star formula. Its three gates survive every restriction. The individual lower bounds alone give no such net-overlap upper bound.

At h=2 an ordinary theta with disjoint arm sets sharing their two poles illustrates the exact ledger: the union has size 4 times the total arm count, equal to the sum of the separate exact theta complexities when each group has at least two arms. The separate output ORs cannot be booked as extra gates on this evidence.

Inside one order-401 two-pole core, the generic cycle has 1604 vertices. A disjoint packing of length-six vertex intervals with no intervening cross edges requires a gap after each interval. Its capacity is floor(1604/7)=229, attained by spacing starting positions seven apart. Even ideal compounding of one gate per such local interval gives only 229 gates in this core.
