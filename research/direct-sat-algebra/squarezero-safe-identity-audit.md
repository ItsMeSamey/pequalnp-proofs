# Independent audit of the square-zero safe-shift identity

Let K=GF(2^d), R=K[y₁,…,yₕ]/(y₁²,…,yₕ²), and zᵢ(s)=s^(2^i). Work in R-valued functions on all of K, so zᵢ²=zᵢ₊₁ with cyclic indexing, including at s=0. For an arbitrary linearized map A and constants cⱼ consider

    P(s)=∏ⱼ(1+yⱼ(cⱼ+Tr(αⱼs))).

Its full y-component is the product of the scalar factors. Since yⱼ²=0 each factor splits into 1+cⱼyⱼ and one term 1+yⱼαⱼ^(2^i)zᵢ per i. Maintain at most one nonconstant factor 1+Bᵢzᵢ per i. Two such factors merge as (1+(a+b)zᵢ)(1+ab zᵢ₊₁). The possible cubic discrepancy is (a+b)ab=0: every element in the augmentation ideal has zero square by characteristic two. The carry ab lies at least one total y-degree above the incoming element because every stored nonconstant coefficient has positive degree. Thus each insertion halts after at most h carries, independently of wraparound or cancellations.

Write Δ(s)=det(D+diag(z₀,…,z_{d−1})) for the Dickson determinant. It equals the binary invertibility indicator pointwise. The coefficient at exponent e from zero through N=2^d−1 is the principal minor of D on positions complementary to the bits of e. For 0<e<N, the sum over all s of s^e Δ(s) is the principal minor on bits(e), since only the complementary exponent reaches a positive multiple of N. For e=0 the constant term sums to zero and the leading coefficient contributes one. For e=N both endpoints contribute, giving det(D)+1. These statements include singular D and make no assumption on symmetry.

Expanding the stored product in the zᵢ and summing weighted by Δ therefore gives det(I+diag(B)D)+∏Bᵢ in R. Multiply by the separate constant factors. For ordinary binary prefix pins use cⱼ=1+desired_bit with the appropriate dual trace coordinates. The full component is the parity of the good completions. With no pins parity is one. A zero-child query suffices per depth; stop at floor(d/2) and enumerate the suffix. The extra product is identically zero when h<d but is necessary for the identity at full depth.

Ranked subset convolution gives polynomial-in-h times 2^h operations per ring product via subset zeta transform, convolution of cardinality layers and Möbius inversion, all over K. In I+diag(B)D the constant part is I. Elementary elimination keeps constant pivots one; each unit 1+δ is its own inverse. Thus the determinant costs polynomially many ring multiplications in d, as do the insertion stages. Total deterministic bit time and storage are O*(2^(d/2)), valid in all degrees for arbitrary binary drift.

The separate regression uses dictionary-valued ring products and an explicit Leibniz determinant. It compares every y-component against independent field enumeration and also checks the carry factorization separately at every field element. Its 290 cases include all maps on GF(4), dense nonsymmetric examples, nonbinary constants, empty restrictions, and depths at and above d.
