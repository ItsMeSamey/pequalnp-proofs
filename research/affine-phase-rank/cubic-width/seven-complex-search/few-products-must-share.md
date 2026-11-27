# Seven-ray lists with at most two block products must have a shared signed Pauli

Write g for normalized three-qubit CCZ. Suppose seven stabilizer rays span g³ with p≤2 block products and no two sharing a signed nonidentity Pauli. After the support-dimension phase gauge in six-must-share.md, every nonzero off-diagonal Gram entry has modulus 1/sqrt(512) and odd eighth-root phase. The r=7 weighted bound in odd-phase-gram.md gives minimum Gram eigenvalue ≥1−(cot(π/28)−1)/32>0.7538. Thus the sum of the seven squared target overlaps must exceed 0.7538. We bound it below this threshold.

Use local classes H (the full real signs differing from g at one point, squared fidelity 9/16), M (the restrictions of g to a plane, squared fidelity 1/2), and the rest (≤5/16). Two H rays share a signed nonidentity Pauli. Two M rays can avoid sharing only on complementary planes. An H and an M share unless the H exceptional point is in the M plane. Two block products with complementary M planes at two sites share the product of the two signed plane-normal checks. These facts are proved in six-must-share.md.

**Exceptional overlap estimates.** For a stabilizer in tripartite local normal form, let k be the total number of Bell and GHZ factors, z its number of GHZ factors. At each party project g into the local Schmidt code and decode the local Clifford. For each shared GHZ label t let its coefficient array be a matrix on the indices of the two incident Bell-edge groups, with Frobenius norm w_i(t). The overlap in absolute value is bounded by 2^(−k/2) times the sum over t of the three-norm products, since a contraction around the three edge groups is a trace of three matrices and is bounded by the product of their Frobenius norms. Edge groups of size zero are treated as one-dimensional. The sum of w_i(t)^2 is at most P_e for a 2^e-dimensional local code, where P_0=9/16, P_1=5/8, P_2=3/4, P_3=1. Thus fidelity is at most the product of the three P_e divided by 2^k, using Hölder and the ordering of sequence norms.

The resulting bounds are as follows.

- Every k≥2 atom has fidelity ≤0.09. For k≥4 the bound is ≤1/16. For k=2 the Bell-pair patterns have exponents (0,2,2) or (1,1,2), and GHZ plus Bell has (1,2,2), all giving <0.09. For two GHZs each local set of four probabilities sums to ≤3/4 with each ≤9/16; the sum of their 3/2 powers is ≤(9/16)^(3/2)+(3/16)^(3/2). Hölder on the four labels gives its square divided by four, <0.09. For k=3 and z≤1 the sum of local exponents is 6+z≤7. If two exponents are three the third is ≤1; otherwise at least two are ≤2. Hence the P product is ≤5/8, giving <0.09. For two GHZs plus one Bell the party untouched by the Bell has sum of cubed norms ≤(3/4)sqrt(9/16)=9/16, the other sums ≤1. Hölder gives squared fidelity ≤(9/16)^(2/3)/8<0.09. For three GHZs each full stabilizer-basis probability vector has collision sum ≤11/32 by Pauli Parseval: one identity and seven squared expectations ≤1/4 each, divided by eight. Cauchy–Schwarz bounds the sum of 3/2 powers by sqrt(11/32), giving fidelity ≤11/256.
- A single Bell has squared overlap at most its spectator's local fidelity times (5/8)^2/2, by the two-party trace bound. Call a Bell H- or M-type according to its spectator ray. Their respective bounds are h=225/2048 and m=25/256; all other Bells have fidelity below o=9/100.
- A single GHZ has fidelity ≤u=49/512. Its two local basis probabilities sum to ≤5/8 with each ≤9/16, so their 3/2 powers sum to ≤(9/16)^(3/2)+(1/16)^(3/2)=7/16. Hölder gives the claim. Unless one of the two GHZ product branches has H rays at all three parties, the bound improves to o. If one party has no H, its 3/2-power sum is ≤(1/2)^(3/2)+(1/8)^(3/2), so Hölder gives at most one half times this quantity to the 2/3 power times (7/16)^(4/3), less than 0.09. If H is present at every site but on different branches, each branch amplitude has a local H-companion amplitude at most 1/4 and its other two amplitudes at most 3/4 each. Their sum divided by sqrt(2) gives squared overlap <0.09.

H-type Bells occupy distinct spectator positions by the H-H test. An M-type Bell at a site holding an H product factor must have its spectator plane through the exceptional point. No second M-type Bell can occupy that site, because its plane would have to be complementary as well. A site holding an M product factor and an H-type Bell cannot hold an M-type Bell: its plane would have to be complementary to the product M while both contain the H point.

If one product has H at two or more sites, any single GHZ with an all-H branch shares a signed check with that product. In fact at each such site its branch and the product H share a local signed Pauli. The other GHZ branch ray is a Pauli translate in the same basis, thus on that site either gives the same eigenvalue (a common local check) or the opposite eigenvalue. In the latter case on two sites their product is a common signed check. This argument works whenever at least two sites have matching signed local checks on the same GHZ branch and the block product, including H-M matches.

**Counting the configurations.** Each count below uses h,m,u,o as above. At most three H-type Bells occur. All other exceptions have bound m; excluding M-type as well leaves bound u. When all-H GHZ branches are excluded, all exceptions outside H/M-type Bells have bound o. Products with any factor outside H,M have bound l=405/4096.

For zero products the sum is ≤3h+4m<0.721. For one product the following upper bounds are all <0.7538:

| Product | Upper bound |
|---|---|
| outside H,M or MMM | 1/8+3h+3m |
| HMM | (9/16)/4+2h+4m |
| HHM, no H-type Bell | (9/16)^2/2+6m |
| HHM, one H-type Bell | (9/16)^2/2+h+2m+3u |
| HHH | (9/16)^3+3m+3o |

For two products with at least one outside H,M use the following bounds, again each <0.7538:

| Other product | Upper bound |
|---|---|
| outside H,M or MMM | l+1/8+3h+2m |
| HMM | l+(9/16)/4+2h+3m |
| HHM, no H-type Bell | l+(9/16)^2/2+5m |
| HHM, one H-type Bell | l+(9/16)^2/2+h+2m+2o |
| HHH | l+(9/16)^3+3m+2o |

Finally suppose both products have only H and M factors. At each site the two types must be H/M, or M/M on complementary planes. No H- or M-type Bell can occupy such a site: H/H sharing or complementary-plane and point-incidence constraints above forbid it in both configurations. At most one site can be M/M, since two such sites would supply a signed joint check. If either product has ≥2 H factors, an all-H GHZ branch is ruled out as above. Otherwise each product has exactly one H (at different sites), since at least two sites are H/M. At the third site the H branch's exceptional point is outside one of the complementary planes, yielding a shared signed local check with that product's M factor. Together with its H site this again rules out such a GHZ. All five exceptions have bound o. The sum of the two product fidelities is at most (9/16)^3+1/8: their H sets are disjoint, and enumeration of the H counts yields largest value at (3,0), followed by (2,1). Thus the total is at most 729/4096+1/8+5(9/100)<0.7530.

This contradicts the Gram requirement in every case. The result forces shared signing but does not assert that the other five atoms or the sign's opposite outcome provide a contradiction.
