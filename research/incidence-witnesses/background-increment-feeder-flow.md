# Complementary feeder flow along monotone background increments

Use physical input slots, no observation fanout, and the conventions of complementary-feeder-singleton-flow.md. Constants may be folded. Fixed constants make no raw increment contribution. For comparable masks B⊆C let d_g=g(C)−g(B)∈{0,1} and let Kraw sum the raw fanouts of labels switched on. Define an absorbed occurrence as either an AND staying false with exactly one newly true operand or an OR already true acquiring a previously false operand. Write Aabs for this count. Define Jboth as the number of gates that switch output and have two newly true operands, counting tied slots separately.

For each gate the number of newly true operand slots less its output increment equals its absorbed indicator plus its Jboth indicator. An unchanged gate can absorb at most one operand, and a switching gate with just one newly true operand contributes zero. Consequently
```
Aabs = Kraw + Σ_internal(f_g−1)d_g − Jboth.
```
This identity also follows by subtracting the true-slot identities on the endpoints. It is not valid to subtract a two-parent toll for every activating AND: an AND whose first operand was already true activates like a unary wire. Its first-arrival toll occurred earlier.

On a chain B₀⊆…⊆B_k, output increments telescope signal by signal. The exact total charge from gate g is (f_g−1)[g(B_k)−g(B₀)] before the joint-activation toll. A physical signal can flip at most once regardless of the number of stages or its fanout; an active gate frozen at the initial background pays zero. Multiple orientations of one interval may be averaged, but the endpoint conclusion concerns consecutive increments on the same realized chain. For arbitrary overlapping stage intervals an activation is paid with its interval multiplicity, not always once.

## Random line prefix and physical gate counts

Use the original promise with unrestricted point payload and at most q selected query lines. Start with all raws zero and no point payload throughout the line prefix. For B consisting of t<q selected lines, P_B is the points outside their union. For a free line ℓ and p∈P_B incident to ℓ the three tests B, B+p, B+ℓ are negative while B+p+ℓ is positive. Trace a gate true on this last input and false on both intermediate tests. At an OR take a true child, which must have the same property. At an AND descend to a child with that property when possible. Otherwise the operands g,h satisfy
```
g(B+p)=1,  g(B+ℓ)=0,    h(B+p)=0,  h(B+ℓ)=1.
```
A raw cannot terminate the trace with the required property. Each such g is a complementary point feeder for (B,ℓ). Let D(B,ℓ) be the set of distinct physical point feeders with any such witness, and T(B)=Σ_free ℓ |D(B,ℓ)|. The oriented receptor AND is an actual absorbing gate on B→B+ℓ: both operands were false, h alone switched on, and the AND remains false. For fixed B,ℓ, distinct feeders have distinct receptors by their unique false operand. On any increasing chain a receptor can appear as this type of sink only once, as its first true operand remains true thereafter.

Sample a uniform ordered prefix of k≤q distinct lines. Conditioning on the current prefix B_t and averaging over the next line gives
```
Σ_{t<k} E[T(B_t)/(N−t)]
 ≤ k U_L/N + Σ_internal(f_g−1)_+ Pr[g(B_k)>g(∅)] ≤ k U_L/N+F.
```
Here U_L is the raw line fanout sum and F is total positive internal fanout excess. This prices every physical shared AND, whatever its width or fanout, only once per realized chain. The left side is also at most the number of physical ANDs, by the distinct-receptor observation. These two upper bounds need not add.

There is an endpoint sharpening. Along a fixed chain choose one receptor per distinct selected feeder, and let Z count selected receptors already true by the final query-only background. Write K for the total number of selected receptors along this chain. With initially zero nonconstant gates,
```
K−Z ≤ Σ_{ℓ selected} f_raw(ℓ)
 + Σ_OR (f_o−1)1[o(B_k)] + Σ_AND (f_a−2)1[a(B_k)]
 − #{ORs with both operands true at B_k}.
```
Indeed K−Z counts a subset of one-high ANDs at the final input. This is the endpoint identity from the singleton ledger evaluated at that whole input. The allowance Z is essential when an early one-high AND later activates. This distinguishes physical AND sharing from reuse of a sink that later becomes true.

## Geometric interpretation

Define A_g(B) as the surviving p for which g(B)=0 and g(B+p)=1. Set h(B,ℓ)=max_g |A_g(B)∩ℓ| including raw wires, and let d(B,ℓ)=|P_B∩ℓ|. For d>0 the complementary feeders cover these d points, so |D(B,ℓ)|≥d(B,ℓ)/h(B,ℓ). Zero-degree terms are zero. On each realized chain the sum of d(B_t,ℓ_next) is exactly the number of points first covered during the prefix. Its expectation is
```
W = N[1−binom(N−q−1,k)/binom(N,k)].
```
For k=q, W∼(1−exp(−1))N. If one weights (stage, chosen line) by the number of its newly covered points, the expected mass on stages with h(B,ℓ)≤H is at most H(kU_L/N+F). Thus its fraction of the total expected first-covered mass is at most H(kU_L/N+F)/W. In particular when s=O(N) and F=o(N), bounded point pools on these conditioned rows can explain only o(1) of this mass. This result needs no fractional-cover normalization. It uses correctness on the specific background tests throughout the prefix; an independently recompiled circuit at each stage would not automatically telescope.
