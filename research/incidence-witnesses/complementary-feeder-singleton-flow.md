# Physical split cost of complementary feeders

Consider a binary monotone physical circuit correct on flag pairs and rejecting pure singletons. Use the directed slot multigraph, counting each input occurrence, including repeated slots. Identify a raw label with its input signal; if an implementation has several raw nodes for a label, sum their outgoing uses. For each signal g let L_g and A_g be its accepted line and point singletons. For each query line ℓ, D_ℓ is the set of distinct physical point-side signals g such that an AND with other operand h has ℓ∈L_h∖L_g and A_g∖A_h contains a point on ℓ. Let T=Σℓ|D_ℓ|. Let U_L count outgoing raw-line operand occurrences. Write f_g for ordinary outgoing internal operand occurrences, excluding the output observation. A root with no ordinary consumers has f=0.

At the pure input ℓ let t_g count true operand slots, and w_g the Boolean value of gate g. Double counting the true operand occurrences gives
```
Σ_g(t_g−w_g) = f_raw(ℓ)+Σ_g(f_g−1)w_g.
```
The left sum counts each AND with exactly one true operand and each gate of either type with two true operands once. Every g∈D_ℓ witnesses an AND with exactly one true operand. Choosing a witnessing AND for each g is injective at fixed ℓ, because such an AND has a unique false operand signal. Summing in ℓ, the both-true toll at an AND a is |L_a| and at an OR o is |L_left∩L_right|. Thus
```
T ≤ U_L + Σ_OR (f_o−1)|L_o| + Σ_AND (f_a−2)|L_a|
          − Σ_OR |L_left∩L_right|.
```
No assumption of prior dead pruning is needed: the double count includes any unused gates with f=0. Output gates reject singleton inputs; an extra virtual observation would only add zero to these evaluations. For an output given by a raw, the definition of D is unchanged and there are no qualifying terms if no ANDs exist. Unreachable auxiliaries obey the same identity; restricting all counts to the trimmed output ancestry is another valid convention. If constants are present, fold them first, or include the outgoing occurrences of each active constant in the raw-side source term for every singleton evaluation.

In particular only positive excess at shared ORs and at ANDs of fanout at least three can pay for T beyond U_L. Under the fractional cover bound M, the geometric feeder inequality of physical-complementary-feeder-count.md gives
```
U_L + Σ_OR (f_o−1)_+ |L_o| + Σ_AND (f_a−2)_+ |L_a|
 ≥ (q+1)N² / [2M(2Ms+N)].
```
This is a physical gate-type Pareto bound. Binary-fanout ANDs contribute nothing. If the OR fanouts are bounded by D and normalized line singleton sizes by m, the number of distinct shared ORs is at least (T−U_L−m Σ_AND(f−2)_+)/[(D−1)m], for D>1. For s≤cN, M=O(log q) and m=O(q log²q/loglog q), with all AND fanouts at most two, this is Ω_c(N loglog q/[(D−1)log⁴q]) for large q. The matching pinning bound permits this m for any fixed polynomial failure exponent using a sufficiently large constant.

Transposing the physical identity does not require a transposed promise for maximal negatives: the singleton tests suffice. If Tᵗ is the analogous distinct line-feeder count over points, the two inequalities add with each gate weighted by |A_g|+|L_g|. For a false-pair cover of size m<N−q−1, every pure activating raw of g lies in that cover: otherwise all its nonneighbors must be covered on the opposite shore. Thus |A_g|+|L_g|≤m, and T+Tᵗ≤U_total+m[Σ_OR(f−1)_++Σ_AND(f−2)_+]. This dual consequence does not assert equal geometric lower bounds for both T and Tᵗ.

## Shifting sharing into ANDs

Fix a true flag (p*,ℓ*). Make one representative for every original node. Raw representatives are unchanged. An original AND becomes the AND of its two representatives. For an original OR with representative operands a,b, emit the four private ORs in the expression
```
((a∨p*)∨b) ∧ ((a∨ℓ*)∨b)
```
and use the final AND as representative. Count each OR physically even when a sibling input has the same raw label. All new ORs have exactly one ordinary outgoing occurrence. The number of gates is #AND+5·#OR≤5s.

The displayed expression equals a∨b∨(p*∧ℓ*). On any nonincidence singleton pair, any independent promised input, or any pure singleton, all representatives equal their originals by induction; the same holds on any assignment missing at least one anchor. On inputs containing the anchor flag the new values dominate the original values and the old output already accepts. All original complementary ANDs persist between representatives, with the same point and line singleton profiles; distinct original feeders remain distinct physical representatives. Hence T cannot decrease. The new private arms increase the point fractional-cover bound by at most one and a bound m on each original signal's false-pair cover by at most one. For a completed arm the old OR's accepted nonincident pairs plus the raw anchor's star cover all its false pairs; for a first arm use the old operand's analogous cover. Pure point supports obey the identical containment. On full positives the private arms need not equal the original ORs.

Thus large feeder reuse need not appear as large physical OR fanout in general normalized circuits: a constant-factor transformation transfers it to shared ANDs while preserving the witnesses and all promised outputs. The transformation does not establish such a normal form for size-minimizing circuits. No gate-minimality claim is needed for the singleton-flow inequality.
