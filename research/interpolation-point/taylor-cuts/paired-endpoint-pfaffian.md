# Pairing ternary factors at residual parity

Suppose a routed bit occurs only in two ternary factors, once in one port of each. The two linked ports are affine in this bit alone. After collecting their coefficients write the factors A₀+YA₁ and B₀+YB₁. Each A_i and B_i is a binary tensor on its own two external port forms. Over characteristic two, summing an ordinary Boolean bit gives

    A₀ B₀ + (A₀+A₁)(B₀+B₁).

For an unread normalized bit, ℓ(1)=ℓ(Y)=1 and ℓ(Y²)=0 instead give

    (A₀+A₁)(B₀+B₁) + A₁ B₁.

These identities follow by expansion; a wrapping coefficient z belongs in A₁ or B₁ as appropriate. Either sum has two terms made only of binary factors, directly realized by the binary gadget in mixed-endpoint-pfaffian.md. In the graph on q remaining nonlinear ternary factors, connect distinct factors whenever they have a qualifying private shared bit. A matching of size ν gives at most 2^(q−ν) Pfaffians if all unmatched factors admit the original two-branch expansion. Maximum matching finds the best disjoint pairing for this guarantee in polynomial time. Distinct selected bits and disjoint factor ownership suffice even when different pairs still interact through external bits. If a pair shares two or three private bits, expanding the local moments on them directly leaves at most two external ports, and one binary factor suffices. The graph test can account for double links with a maximum-weight matching, weighting a one-link edge by one saved exponent and a two-or-more link by two.

## Exact four-terminal test

For a four-port polynomial on independent formal reference ports, let f(S) be the coefficient of the product over S. A graph with one terminal for each port should contribute f(S) when exactly those terminals are consumed externally. Work over a field of characteristic two. The identically zero signature has a trivial realization. Otherwise choose P with f(P) nonzero and put g(D)=f(P symmetric-difference D)/f(P). A pendant edge of weight one terminating in a new zero-monomer terminal swaps the two states of any port. Thus it suffices to realize g, now indexed by the terminals retained internally with g(empty)=1. Set

    m_i = g({i}),   w_ij = g({i,j}) + m_i m_j.

Test all triples and the four-set against the matching polynomial of the corresponding induced graph with these monomer and edge weights. Success constructs a realization directly, restoring the pivot flips and scalar. The test is necessary even with arbitrary private internal vertices. For a monomer-dimer graph the symmetric matrix with diagonal entries equal to the squared monomer weights and off-diagonal entries equal to the edge weights has determinant equal to the squared matching sum. Permutations containing long cycles cancel in reversal pairs, and transpositions square edge weights. Since the internal-only matching sum is nonzero after normalization, its principal matrix is invertible. The Schur complement on the four retained terminal positions then has minors g(D)^2. Its diagonal entries must be m_i², and its off-diagonal entries must be w_ij by the two-by-two minor equation and injectivity of squaring in a field. This proves necessity. The same test over F₂(z) permits polynomial port coefficients, with denominators cleared before native jet truncation.

## Native one-link census

The checker computes each pair's four-bit Boolean truth table, converts to multilinear coefficients by binary Möbius inversion, and applies the test above. It exhausts OR and COPY at each factor, all six independent port complements, and both ordinary and normalized central moments. With unit routing coefficients all 512 nondegenerate four-external-port signatures fail the one-graph test. The two-product formulas hold in all cases. For the corresponding formal z-wrapped ports the same obstruction holds before truncation if specialization z=1 gives that unit-coefficient signature. Indeed choose P nonzero at z=1. All normalized identities in the necessity test have only powers of f(P) in their denominators and hence specialize there. The result addresses the full independent formal signature. Identified or fixed external ports, cancellation after the remaining contraction, and identities special to a truncated quotient can change the result. There is no lower bound here on directly computing the global scalar.
