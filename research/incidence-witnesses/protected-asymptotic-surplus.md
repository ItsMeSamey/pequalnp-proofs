# Asymptotic surplus in the protected iteration

Let the initial size allowance be 4N−4+k, with k=floor(cN), where N=q²+q+1. Keep the bilateral normalization and use groups on at most three sites per shore as in protected-dense-signature-401.md. The point and line bounds give S₀≤2k+O(q). Indeed the point unedited term is at most (4N+k)/floor((q−3)/2), and the line census can choose h=ceil(N(q+1)/(qW)) with W=(q+1)ceil(log₂(q+1))−2^ceil(log₂(q+1)); thus h=O(q/log q). The other additive census terms are O(q).

Fix t≥8 and ct<1. Write z for spent surplus and m for the number of earlier batches of actual deletions. Each deletion batch costs at most t sites and pays at least one literal zero-flow surplus before pruning; m≤z≤k. A batch retains at least three neighbors by the protected marking rule. There are O(q) marked sites because T≤tk and the squared geometry threshold (q−t−1)² exceeds T by Ω(q²).

Let n denote current raws, p protected raws, u designated unprotected sole AND owners, S total sole raws, and G=F+E the sum of internal and raw positive fanout excess. Separate zero propagation from trimming. Each batch surplus accounts for at most one newly sole site or newly sole-OR site per unit under propagation; all other simplifications account for at most two per eliminated gate. Hence
```
n ≥ 2N−tm
p ≤ 2z−m+O(q)
u ≤ S ≤ 2k+2z−m+O(q)
G ≤ S+k−z−3.
```
These bounds apply separately to each count; no assertion of disjointness between p and S is needed.

With no further saving, the number of OR groups is at least (n−p−u)/2. It is at most 1+u+3G+2[2(n−p)−u]/(t+1)+4p. For the bracket, unprotected ordinary raws each supply at most two small-source tokens while each sole AND supplies at most one. Thus it suffices that
```
(n−p)(t−7) > (3t−1)u + (t+1)(6G+8p+2).
```
Substitution increases the adverse bound at larger z, so set z=k. After moving the loss tm in n to the adverse side, that side becomes (54t+22)k+(t²−25t−6)m+O(q). Maximizing over 0≤m≤k proves the bound for all fixed c strictly below 2(t−7)/[54t+22+max(0,t²−25t−6)] with ct<1. At t=26 the cutoff is 19/723 and ct<1 throughout. Letting c increase to the cutoff gives liminf s/N ≥ 4+19/723 along plane orders for this scalar promise. This is a linear-in-N bound.

## Current sole-OR protection

Keep the theta and geometric marks permanent. At each round additionally exclude just the B current sole-OR raws. Released former sole-OR sites are safe because the reader compensation uses only the prebatch type. Then p≤B+O(q), u≤S−B, and B≤2z−m. The adverse coefficient of B is (t−7)+8(t+1)−(3t−1)=6t+2>0. At z=k the previous inequality improves to
```
2N(t−7) > (48t+24)k + (t²−22t−7)m + O(q).
```
At t=23 the worst case m=k gives c<4/143. Thus the lower limit is at least 4+4/143.

## Exact adaptive order-402 check

The ceiling of Nq/100 is 651269. The contrary cap gives k=3244, h=53, S₀≤13135. Fix permanent geometric threshold 42 (protect sites reaching this degree together with three surviving neighbors), so H=361 and batches up to 40 are safe. At stage z choose a nondecreasing batch cap t(z) using all states m≤z. Earlier deletion stages occur at distinct smaller surplus values. Write L(z) for the sum of all earlier caps. The number of sites actually deleted is at most T=L(z)−L(z−m). Consequently geometric protection costs at most 808+4 floor[T(H−1)/(H²−T)]. Set B=2z−m, S=13135+B, n=2N−T, p=B plus geometric cost, u=S−B and G=S+k−z−3. These are joint adverse substitutions by the positive coefficient of actual B displayed above. Set A=n−p and V=6G+8p+2. Each state requires t(A−3u−V)>7A−u+V. The finite checker verifies a positive coefficient, picks the least integer satisfying all states and the nondecreasing constraint, and verifies the cap stays below 40. Largest required cap was 25. Final cap prefix sum was 58110. Hence k+1 rounds are available, a contradiction. The order-402 implication is conditional on the existence of that plane.

## Outdegree discount and periodic resets

A protected sole-OR raw contributes zero fanout excess. The previous count of nodes with two large operands may therefore subtract B, and the group upper bound subtracts 2B. The scaled adverse side for current-only protection becomes (40t+16)k+(t²−18t−3)m+O(q). The remaining B coefficient is 2t−2, positive. At t=22 the cutoff is 10/327.

To eliminate the leading protection term, let block=ceil(N^(3/4)). Before the next counting round, whenever spent surplus since the last reset reaches block, hoist the OR spines of the current sole-OR raws outside the permanently protected geometric set. A literal untrimmed hoist never increases the count of sole raws or changes an untouched sole-AND raw into a sole-OR raw. Transfers of off-spine occurrences preserve uses. Treat any later trimming separately. There are at most floor(k/block) resets, since disjoint intervals each spend at least block. Further pruning may itself trigger another reset.

Initially demand correctness only on independent b-by-b masks, with b=3+floor(k/block); the bilateral construction supplies this for all sufficiently large q. Each reset consumes at most one unit of this allowance by the sparse OR-hoist argument. Permanently mark current vertices when their degree reaches b+t+2 or below, reserving themselves and three surviving neighbors. A new mark has at least three surviving neighbors, and every unmarked reset candidate has degree >b. The deleted-neighborhood threshold is H=q+1−(b+t+2)=q−o(q); as ct<1 the number of marks is O(q). The geometric protected sites may retain sole OR readers. All other sole ORs present after a literal reset have been removed, and between resets at most 2 block new ones arise. Thus p=o(N) at each counting stage. The raw-use census and cumulative surplus estimates survive resets; in particular u≤S≤2k+2z−m+O(q), and G≤S+k−z−3.

Substituting p=o(N) in the live-round inequality now gives the sufficient inequality
```
2N(t−7) > (36t+20)k+(t²−16t−5)m+o(N).
```
At t=21 the right side is at most 876k+o(N); ct<1 throughout the resulting admissible range. Taking limits from below gives liminf s/N≥4+7/219.
