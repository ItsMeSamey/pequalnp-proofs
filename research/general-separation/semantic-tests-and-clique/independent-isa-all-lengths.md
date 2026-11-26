# All-length hardness for densely tested independent lookups

There is one explicit balanced language in P, with O(N) bounded-fan-in shared gates at every length N, for which each nontail estimate below holds at every sufficiently large N. An individual Boolean atom of size at most N(log N)^b for any fixed b has uniform prediction advantage at most 2^(−N^(1−o(1))) for an arbitrary binary formula or acyclic deterministic single-bit query program, and at most 2^(−N^(1/2−o(1))) for an acyclic existential program with arbitrary successor sets. Here an exponent β−o(1) means that β−ε holds eventually for every fixed ε>0. A separate explicit AND language gives corresponding reciprocal sound-cover and exact signed ℓ₁ bounds. Neither conclusion bounds unrestricted shared circuit size.

## Saving the per-bank factor in the moment estimate

Adopt the notation of [the signed-weight proof](independent-isa-signed-weight.md). In a slice there are r independent banks each with m=2^t payload bits, P=2^floor(log₂(m/t)) pointer rows and one primary index. Let D=1+W/(rP). Choose a threshold L≥1. After pinning selected heavy banks and nonselected words, s≥1 light banks contribute a mask on their selected words with at most sL total live occurrences. The Rademacher estimate for the expected maximum over H masks is
[
 H^{1/p}(C\sqrt{p/m})^s,qquad p\ge2.
]
Set p=max(2,ceil((log H)/s)). Then H^(1/p)≤exp(s), including H=1. The factor is absorbed into the constant raised to the s-th power. For formulas, log H=O(sL). For unrestricted existential programs, log H=O((sL)²). For deterministic acyclic programs, each live node and answer has only one first live node or terminal, as does the start. The contraction on named live nodes therefore has O((sL)log(sL+2)) bits. All constants are absolute. The heavy event probabilities and independence in the signed-weight proof now yield, for the absolute correlation of a single atom with the product Z of addressed payload signs, upper bounds equal to the r-th power of the respective brackets

* D/L + C sqrt(L/m) for formulas;
* D/L + C sqrt(L log(rL+2)/m) for deterministic programs;
* D/L + C sqrt(r)L/sqrt(m) for existential programs.

These estimates hold for fully interleaved atoms, with the actual residual mask allowed to depend on every free payload bit.

An analogous estimate for any one-sided atom uses support instead of signs. After pinning heavy banks, let U be its realized accepted subset of [m]^s. For fixed nonempty candidate U, soundness requires all positions in all its coordinate projections to be one in their respective payload banks. If v is the sum of those projection sizes this has probability 2^(−v). The maximum v among compatible nonempty dictionary masks has L^s norm ≤log₂H+Cs, by a union bound and its exponential tail. Since |U|≤(v/s)^s, the conditional probability of acceptance is at most [C(1+(log H)/s)/m]^s. The rule is trivial when no light bank remains. Averaging independent heavy flags, as before, gives absolute atom probability bounded by the r-th power of

* D/L + C L/m for formulas;
* D/L + C L log(rL+2)/m for deterministic programs;
* D/L + C rL²/m for existential programs.

For covers, divide the target's accepting probability 2^(−r) by such a per-atom bound.

## A single pair of layouts at every input length

Divide the N coordinates into halves of lengths floor(N/2) and ceil(N/2). For each half independently let H₀ denote its length, k=floor(log₂ H₀) and u=ceil(sqrt(k)). In the first half set t=u. In the second set t=ceil((k+u)/2). In each case m=2^t, and r is the floor of H₀ divided by the exact bank length log₂P+Pt+m. Parse precisely these r complete banks and ignore the remaining bits. For the finitely many small N for which a layout is missing, use the first bit for N≥1. All lengths and integer square roots are uniformly computable; scanning and ordinary multiplexing take polynomial time, and the explicit bounded-fan-in circuit at each length has O(N) gates. At large N, r=Θ(H₀/m) and D≤k^{O_b(1)} for W≤N(log N)^b, since P=Θ(m/t) and H₀=Θ(N).

In the first half, m=2^u and r=2^{k−O(sqrt(k))}. In the second, r/m≤2^(1−u) since m²≥2^(k+u) and H₀<2^(k+1); also r=2^{k/2−O(sqrt(k))}. Choose L=ceil(2^(u/8)) in each. For formulas and deterministic programs in the first half, log(rL+2)=O(k). Every relevant signed or sound bracket above is ≤2^(−c u) eventually, since D is polynomial in k and u grows like sqrt(k). For the existential program in the second half, sqrt(r/m)L and (r/m)L² both decay as 2^(−Ω(u)), and the same holds for D/L. Hence all relevant brackets are ≤2^(−c u) for some absolute c>0, with a starting threshold depending on b. In the first half ru=N^(1−o(1)) and in the second ru=N^(1/2−o(1)).

For the balanced target take the product of the two halves' signs and convert this sign to a bit. Its sign is mean zero under uniform inputs. Condition on all coordinates in the second half when proving the formula or deterministic-program prediction bound, and on the first half for the existential-program bound. An arbitrary atom may interleave the halves. Pinning the outside coordinates simply supplies constants to the same residual-dictionary proof; the budget remains W. The fixed outside sign has unit absolute value. Therefore a single explicit target has all claimed correlation rates on all large lengths. The [average absolute error and normalized margin consequences](independent-isa-xor-margin.md) follow with these δ: E|G−B|≤1/2−γ implies Σ|weights|≥γ/δ, a correct strict threshold has normalized margin ≤δ, and polynomially bounded integer weights then require at least 1/(2δ·poly(N)) atoms.

For the AND target take the AND of both halves' bank outputs. For the corresponding model hardwire all payloads of the other half to one, leaving its pointers arbitrary fixed. A sound cover restricts to a sound cover, and an exact signed real equality restricts to an exact signed equality with the same weights (or smaller ℓ₁ after merging duplicates). For a cover the uniform slice measure is 2^(−r) and each atom has mass ≤2^(−c u r). For signed equality the slice target's correlation is 2^(−r) and each atom's absolute correlation is ≤2^(−c u r). Thus sound-cover size and exact signed absolute weight are both at least 2^Ω(ru). Nonnegative exact representations induce sound covers. The polynomial-weight threshold lower bounds concern balanced XOR only: AND itself has a small threshold by summing one disjoint pointer-row indicator per bank/row and checking that every bank accepted.

For the unbounded-magnitude signed sparsity question, the general rational coefficient normalization only yields log(weight)≤O(S log S) for a representation with S summands after a change of weights. Near-exponential weight accordingly gives an almost-linear lower bound by this route, still short of superpolynomial sparsity. An arbitrary shared Boolean circuit computes both languages with O(N) gates.
