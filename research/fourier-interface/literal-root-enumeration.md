# Size of the literal root enumeration

In the October 25 version of Appendix D, consider every sufficiently large active root with edge count M=s. At t=1 the number of distinct feasible mode exponent tuples is

    2^{Θ(s/√log s)}.

This counts the specified enumeration before any coefficient or child value is tested. It applies for each interpolation value ζ. It gives no lower bound on the time to evaluate the sum after pruning or algebraic regrouping. [Pinned source, parameter settings and packing](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex#L68-L160)

Let λ=⌈log₂ s⌉, u=⌊λ/131072⌋, a=2u, L=2^a and r=64. At t=1 we have i=0, D=L and positive multiplicity. With h=⌈3M/u⌉ the precision satisfies p_t=p+8hL+8M(a+1)>24ML/u. [Precision in the pinned source](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex#L234-L250)

Among the D_arr=r^(2a) ordered pair-label classes, precisely D_arr/r have equal symbols at coordinate zero. Each class has at most 3M/D_arr real edges. The remaining classes therefore contain at least (61/64)M real edges. Let K be the number of occupied packets with unequal symbols at that coordinate. Each packet holds at most L edges and there are at most 3M/L packets, so (61/64)M/L ≤ K ≤ 3M/L.

Choose one nonempty tile in each of these K packets and set B=⌊L/√u⌋. The expansion introduces a mode of each weight j=1,…,B for that tile, since B<p_t. Choose exponents zero or one independently on those KB modes and zero elsewhere. Every selection has weight at most K·B(B+1)/2 ≤ 3ML/u < p_t. The literal enumeration visits all 2^(KB) selections. As B≥L/(2√u) for sufficiently large s, its size is at least 2^((61/128)M/√u). The source's partition-count upper bound at this node is exp(O(M/√u)), and u=Θ(log s). [Mode creation and enumeration](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex#L392-L454)

## A four-port coefficient test

At the permitted evaluation ζ=1, t=1, we have T=2L+1. An occupied packet with at least four real slots exists for large s since there are at most 3M/L packets. Leave four real column bits free and pin all other columns to zero. Pin two real rows to one and sum the remaining row bits with unit weights. These unary restrictions are realizable on a matching. The packet then contributes f(x)=(Σ a_i x_i)(Σ b_i x_i), where a_i and b_i are the entries W_xy(T) in the two selected rows. Evaluating this expression for fixed x exactly aggregates its formal modes. Each W entry is computable in polynomial bit time at the stated precision. [Deformed contraction and entry computation](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex#L163-L225)

In the Boolean multilinear coefficient basis the even projection has q_∅=q_1234=0 and q_ij=a_i b_j+a_j b_i. The alternating combination q_12 q_34−q_13 q_24+q_14 q_23 equals 2(a_1 a_3 b_2 b_4+a_2 a_4 b_1 b_3). All kernel entries have the same sign over the rationals because T exceeds every slot difference, so this quantity is nonzero. Each W has numerator and denominator of O(L log L) bits from its grid-product description. Its reduced denominator is odd by integrality. A common odd denominator over the constant number of terms still has O(L log L) bits, as does the cleared numerator. Since L log L=o(p_t), the violation survives reduction modulo 2^p_t. Thus this even tensor violates the four-leg Pfaffian identity in this coefficient basis for every leg ordering. The test concerns one specific representation and says nothing about alternative bases, decompositions into several signatures, or global algorithms.

## Version, parameter range, and an explicit root threshold

The Appendix D file is byte-identical at the October commit above, the last main-branch commit dated on or before November 24 UTC (f5702854040e97fa7675c21ba37a9608f5f92dd3), and commit 3344da59991ed94f9ba711217b29c1d760badfa6. Each copy is 27,544 bytes with SHA-256 671642d7b53154d92344e8c4be0240f18929632ebcfdf73b07c3e9939b873860. This comparison covers that specific Appendix D source. [November 24 copy](https://github.com/openai/math/blob/f5702854040e97fa7675c21ba37a9608f5f92dd3/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex)

In the theorem's input interface choose C=1, M=s, any 1≤P₀,ℓ≤s, and any bipartite input meeting its degree, vertex-count, and entry-evaluation conditions. A matching on s edges with constant unary tables realizes every s, even with P₀=ℓ=1. For the displayed root-loop argument, λ≥2^100 is a conservative sufficient threshold for the numerical root inequalities: u≥λ/2^18≥λ^(4/5), H<s, L≤2^(λ/65536), D_arr≤2^(12λ/65536), and Δ≤2·s^(9/10). Since s>2^(λ−1), these imply s≥2 D_arr² Δ, s≥L D_arr and 2L≤Δ. Also B≥1 and B≥L/(2√u). At t=1 the required multiplicity is q_t=hu≥3M, and p_t>24ML/u even at input precision one. The numerical threshold refers to the root loop once the recursive algorithm is invoked. If an implementation chooses an additional fixed finite-size direct-summation cutoff, its threshold must also be exceeded. [Input interface](https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex#L24-L51)

## Evaluating all modes with a supplied port algebra

Fix one required evaluation T and its working ring R at precision p_t. Suppose we have a commutative unital R-algebra A, free of dimension D with explicitly computable structure constants, port weights c_j(0),c_j(1) and r_i(0),r_i(1) in A, and an R-linear readout φ. Require the exact representation

    A_rows(Y) B_cols(X) = φ( ∏_i r_i(Y_i) ∏_j c_j(X_j) )

for all independent port assignments in the deformed problem. This certificate must hold for the lifted factors at the evaluation precision. A representation only modulo the original precision cannot in general be lifted entrywise through an arithmetic identity. The computation below assumes the supplied representation as a promise.

For a packet call a row active if r_i(0) differs from r_i(1), and suppose at most h rows per packet are active. Pull out the common weight from each inactive row. Write δ_i=r_i(1)−r_i(0). In the commutative ring A[t_1,…,t_h]/(t_i² for every i), form

    ∏_i(1+t_i r_i(0)) · ∏_j( c_j(0)+c_j(1)∏_i(1+t_i δ_i W_ij(T)) ).

Extract the coefficient of t_1⋯t_h. For any fixed column assignment X, multiplying the factors of each t_i first shows that this coefficient is the column weight times ∏_i(r_i(0)+δ_i Σ_j W_ij X_j), precisely the contribution obtained by summing the row bits. Including the inactive constants and multiplying these packet coefficients in A before applying φ gives the full deformed contraction. This identity sums all modes simultaneously. The number of live columns or the number of original vertex incidences across a packet cut can grow.

Each packet costs poly(s,D)·4^h arithmetic operations in R by dense square-zero multiplication and ordinary structure-constant multiplication. Each R-operation costs polynomially many bit operations in s,p_t,e,ℓ. At the root these parameters, the number of packets, nodes, interpolation points, and the cost of Hermite recovery are polynomial in s. Consequently a polynomial-rank, polynomially constructible and readable certificate at every root evaluation, with h=O(log s), gives polynomial bit complexity for this promised class. The calculation needs no division by factorials. It directly evaluates the weighted arithmetic contraction.

For example a bounded number of distributed Hamming-weight observables can be recorded by adjoining one truncated monomial marker per observable with truncation exceeding its maximum count; the algebra dimension is a product of these polynomial counts. A final linear functional on the joint histogram can apply arbitrary supplied weights. Port contributions are coupled across arbitrary packet cuts. This certificate may compress an otherwise wide boundary and makes no claim of polynomial rank for general CNF tensors.
