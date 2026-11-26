# One collision for q² forced-marker flags

In a projective plane of order q≥2 take a point d and the q+1 incident query lines v,x₁,…,x_q. Write D for the OR of all point inputs on v and S_i for the OR of the q point inputs on x_i other than d. Compute

    g₀ = v AND D
    g_i = x_i AND (S_i OR D)
    L = g₀ OR ⋁_i g_i
    R = d OR v OR ⋁_i (g_i AND S_i).

Output L AND R, joined by OR with the standard incidence terms for all lines outside the pencil. This computes incidence on the full cube. A true g₀ or a true g_i AND S_i supplies a hit directly. In the remaining case L supplies a true g_i. If R holds via d, x_i hits d. If R holds via v, either x_i hits S_i or v hits D. Conversely each single pencil flag activates L and R.

Each x_i has one raw reader. Its guard accepts the complement of x_i through D. On forcing g_i to one with all other query inputs off, the output equals d OR S_i. At any p∈S_i only g_i witnesses L and only g_i AND S_i witnesses R. Every proof must use g_i on both sides of the very same final AND. There are q² such flags, one family of q for each of q distinct interventions.

The gadget is locally irredundant under bypass of a gate to either operand. For g_i, bypass to x_i accepts the two lines x_i,v on empty payload. Bypass to the guard accepts d on empty query. Each guard needs S_i on its private off-d flags and D on its flag at d. For g₀, bypass to v accepts v alone and bypass to D accepts d alone. For g_i AND S_i, bypass to g_i accepts x_i with payload z∈v minus d; bypass to S_i accepts another x_j with payload z and p∈S_i. Both miss x_j. Dropping L accepts d alone and dropping R accepts x_i with payload z. All OR tree branches are necessary on private flags: x_i with p∈S_i, x_i with d, and v with p∈D suffice for the pencil gates. The private flags for the outside-line terms witness all remaining OR branches. Dropping the query operand from an outside-line AND accepts a point alone; dropping its point operand accepts a line alone. These witnesses all use at most two lines. The construction thus survives this local normalization under either promise. It gives no optimal-size or global-refactoring lower bound.
