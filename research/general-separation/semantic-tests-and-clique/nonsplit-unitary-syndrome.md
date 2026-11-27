# Exact pinned search and counts in a nonsplit GF(4) family

Use K=GF(4), conjugation bar(a)=a², and ω²=ω+1. In a supplied systematic chart a length-2m Hermitian self-dual code has words (u,Uu), u∈K^m, U†U=I. Each site has an explicit allowed list: remove the physically forbidden symbol and intersect with the actual image of every pin on that site. In particular a coordinate swap sending the physical pin (1,0) to (0,1) changes the singleton list accordingly. This formulation permits any number of pins.

Suppose a supplied monomial matrix P (one nonzero per row and column) has rank k for U−P. Gaussian elimination finds a factorization U=P+BC with C of size k×m. For each s∈K^k, enforce Cu=s. On this branch the output vector is Pu+Bs. Each input coordinate and its matched output give a list of at most four allowed values for that one input: test its own list and its output's list after applying the known nonzero multiplier and offset. Starting with sum zero, process the m lists by dynamic programming on the partial syndrome in K^k, adding the corresponding column of C times each allowed input value. Keep counts or store a predecessor for witness recovery. At the last layer take state s. Different branches have disjoint words. Thus the exact count and a witness take poly(m)16^k bit time (counts have O(m) bits), polynomial when k=O(log m). This checks a supplied systematic presentation and P; optimizing the rank over presentations is a separate problem.

## An unbounded connected family outside locally CSS charts

For any odd m≥3 take a vector v with all entries nonzero and Σvᵢ=0, using 1,ω,ω² and then repeated equal pairs. Set

    U = I + ω v v†.

Now v†v=1. Expanding U†U, the nonidentity coefficient vanishes since ω+ω²+ω³=0. Moreover U1=1. The code contains every constant word, and k=1 with P=I. All entries of U are nonzero. Its diagonal entries are ω², and Uᵢⱼ=ωvᵢ bar(vⱼ) off the diagonal.

To verify that these are genuinely nonsplit charts, write any binary-linear map on a single K symbol uniquely as z↦αz+β bar(z). A sitewise endomorphism of the code must satisfy

    diag(α_out) U = U diag(α_in),
    diag(β_out) bar(U) = U diag(β_in).

These equalities follow by varying u, since z and bar(z) are independent as functions over K. Nonzero entries throughout U force all α to be equal. Either every β vanishes or every β is nonzero. In the second case the entry ratios Uᵢⱼ/bar(Uᵢⱼ) would factor as a row multiplier times a column multiplier. Multiplying row i of U by vᵢ⁻¹ and column j by vⱼ preserves this factorization property and leaves diagonal ω² and off-diagonal ω. A rectangle with rows i,j and columns i,k for three distinct indices has exactly one diagonal entry. Its cross ratio is ω²/ω=ω, so the corresponding rectangle of conjugation ratios has cross ratio ω/bar(ω)≠1. This contradicts factorization. Hence the site algebra is precisely scalar K, with no nontrivial idempotent. A locally CSS chart would admit the conjugate of its projection onto the first binary coordinate at every site, a nontrivial idempotent. Also no decomposition into disjoint site components is possible: projection onto a component would be another such idempotent. [Site algebra and the CSS projector](connected-site-endomorphism-f4.md)

## Realization in the physical graph model

Identify K symbols with pairs in GF(2)^2 using basis 1,ω. The trace of the Hermitian pairing gives the site symplectic pairing. Every codeword has even weight by Hermitian self-orthogonality, and its coordinates sum to zero by orthogonality to the constant-one word. If the numbers of symbols 1,ω,ω² are reduced modulo two, their parities must all be equal by the coordinate-sum equation, and their total is even, so each is even. In particular the number of (1,1) symbols is even and the site quadratic Σ xᵢyᵢ vanishes on the code.

For completeness a graph chart can be constructed with only swaps at selected sites. The coordinate-function pairs span at least |S| dimensions for every subset S of sites: the kernel of their projection is isotropic on the other 2m−|S| sites and has binary dimension at most 2m−|S|. Thus an independent transversal exists and is found by linear/partition matroid intersection. Swap its coordinates into the first positions. Projection onto these positions is invertible, giving graph(A); the symplectic identity makes A symmetric and the vanishing site quadratic makes its diagonal zero. The graph is connected by the component-projection argument above. These swaps preserve the forbidden (1,1) at every site; transport each physical pin exactly in the reverse direction before the syndrome algorithm. This gives arbitrarily large connected loopless graph instances, outside local CSS, with a deterministic polynomial count and witness algorithm for all named pins. [Rado’s independent-transversal theorem](https://doi.org/10.1093/qmath/os-13.1.83)
