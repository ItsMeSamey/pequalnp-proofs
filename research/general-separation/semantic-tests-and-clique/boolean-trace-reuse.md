# Multiplication shared across restrictions of the same Boolean circuit

Fix a binary XOR–AND circuit C. Split its inputs into selectors and surviving variables x. Choose any set of selector settings. Use a single common domain for x, which may itself be a promise. Work over F₂ in the space of functions on that domain. Set V₀ equal to the span of constants and surviving input coordinates. In topological order, let V_j add to V_{j−1} all functions of x obtained by fixing the selectors in the output of AND gate j. Write d_j=dim V_j−dim V_{j−1}.

**Exact cost for computing the full trace.** The fewest scalar AND gates computing every wire value of C at every selected setting, all as functions of the same x, is Σ_j d_j. For the upper bound choose d_j restricted outputs from gate j that extend a basis of V_{j−1}. Their operands belong to V_{j−1}, since all earlier restricted AND values are already available and the intervening operations are affine. Compute the chosen products and recover the other outputs by free XOR. For the lower bound, r scalar ANDs can supply at most r function directions modulo V₀, even with arbitrary depth and reuse. The argument uses equality of functions on the actual domain. Original scalar gate j costs only one AND in C regardless of d_j.

**A universal low-overhead conjecture fails.** Consider the precise conjecture that extracting all restrictions on k selectors of a size-r circuit has joint scalar multiplicative complexity polynomial in k+r. For f(s,x)=∏_{i=1}^k (x_i+s_i), the original circuit needs exactly k−1 ANDs, by Boolean degree and the product circuit. The selector restrictions are all 2^k point indicators on x. The conditional squarefree coefficients in s are all monomials ∏_{i∉S}x_i. Each of the two lists spans the entire function space. Computing either list requires at least 2^k−k−1 ANDs, and building each degree-at-least-two monomial once attains that bound. The same upper bound holds for any number of outputs on k surviving bits. Even the degree-j coefficient list has binom(k,j) independent outputs modulo affine functions when k−j≥2. This obstruction applies to extracting exact Boolean differences.

For the [Cauchy phase](cauchy-boolean-price.md), consider its circuit with one layer of products of affine forms. Fixing selector groups changes a given gate's product by an affine function of the surviving bits. Thus d_j≤1 for every gate of that implementation, simultaneously for all settings of any fixed selector group set. Exponentially large real spectral norms coexist with inexpensive simultaneous restricted trace evaluation.

## Exponential expansion inside polynomial circuits for sparse HC

For the Boolean predicate on row-one-hot inputs that checks whether the successor map is one directed N-cycle, fix k entire row labels as selectors. The space spanned by all residual output functions has the communication-matrix rank over F₂. For 0<k<N this rank equals

    Σ_{m=1}^{min(k,N−k)} C(k,m) C(N−k,m) 2^{m−1}.

The image-set block proof in [the characteristic-zero calculation](onehot-hc-rank.md) is field-independent up to the rank of a block. Its core matrix has rows and columns labeled by bijections on m points, with a one when their product is an m-cycle. It is a submatrix (up to index inversions) of the ordinary matching-connectivity matrix on 2m vertices: use the two bipartite perfect matchings in the alternating cycle. At m=1 the matrix is [1]. Cygan, Kratsch and Nederlof prove the larger matrix has F₂-rank 2^{m−1}. [Primary theorem](https://arxiv.org/abs/1211.1506)

For the reverse inequality, let P_S be the ordered product of the adjacent transpositions indexed by S⊆[m−1]. Use row P_S and the column giving the product with P_{[m−1]∖T}, for each T⊆[m−1]. If T is not contained in S, both permutations preserve an initial segment across a missing adjacent transposition, so their product cannot be a single cycle. For T=S the product uses each edge of the path once and is an m-cycle. Indeed, as each transposition is applied, its endpoints lie in distinct components of the earlier edge forest and hence in distinct permutation cycles. It joins those two cycles. The resulting minor is unitriangular in a subset order. This gives 2^{m−1} independent dimensions and the displayed formula.

For an equal split N=2k, the rank is (D_k−1)/2, where D_k=Σ_m C(k,m)²2^m is the central Delannoy number. Its order is Θ((1+√2)^N/√N). Divide C(k,m)(√2)^m by (1+√2)^k to obtain the mass of a Binomial(k,p) with p=√2/(1+√2). The sum of its squared masses is Θ(k^(−1/2)), by the Stirling mode bound and Cauchy–Schwarz on a window of O(√k) containing at least half the mass.

The surviving k one-hot rows give dim V₀=1+k(N−1), since the constant and N−1 symbols per independent row form a basis of the additive functions. Consequently every r-AND circuit for this promise has a gate with

    d_j ≥ ((D_k−1)/2 − 1 − k(N−1))/r.

In particular, every polynomial-size circuit for this polynomial-time predicate must use an AND gate whose restricted outputs supply (1+√2)^N/poly(N) independent new functions. This holds for every efficient implementation of the promise predicate. The [one-way protocol and construction](onehot-hc-sketch.md) give Ω(N log N) scalar ANDs and an O(N log⁴ N) scalar upper bound for the original predicate.

## What a separation using this measure would require

For a fixed selector family and scalar target F, let B be its residual output span dimension modulo V₀. A theorem bounding d_j≤U on every gate of some normalized implementation of size O(r^c) of each r-gate circuit would yield r=Ω((B/U)^{1/c}). A superpolynomial ratio for an explicit uniform NP target under a proven polynomial-overhead normalization would separate NP from P/poly and hence P from NP. The proposed universal normalization with polynomial U is false, even for the native one-hot HC target just analyzed, regardless of polynomial blowup. Qualifying the normalization to a different, structured set of restrictions would require a separate proof. The all-wire identity alone supplies no such ratio.
