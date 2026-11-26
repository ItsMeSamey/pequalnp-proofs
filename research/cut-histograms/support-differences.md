# Bounded-degree Boolean tests on the support of a sparse Walsh polynomial

Let g(x)=Σ_a c_a(−1)^{a·x} on F₂ⁿ have s nonzero distinct Walsh coefficients over a fixed odd-characteristic field with efficient arithmetic. Let P be a Boolean polynomial of degree d given in algebraic normal form, and fix b∈F₂. For fixed d there is a deterministic polynomial-time algorithm finding x with g(x)≠0 and P(x)=b, or certifying nonexistence. This covers every fixed finite abelian 2-group times any fixed abelian group of odd prime-power order as an unsigned marker group for an arbitrary binary affine code. In particular all fixed moduli 2^k p^a with p odd are covered.

For modular linear systems, compare the quasipolynomial bound and remaining range with at least three factors of two in [Brakensiek, Gopi and Guruswami, Theorem 1.1](https://arxiv.org/abs/1902.04740). The fixed-modulus code-support result here gives a deterministic polynomial bound in that range.

## A connected support graph

If s=0 reject. Pick one Walsh frequency a₀. Find at most ceil(log₂ s)+1 directions such that each nonzero difference a+a₀ is nonorthogonal to some chosen direction. Greedily choose a direction separating at least half the remaining differences: a uniform direction has that expectation; fixing bits by conditional expectations attains it deterministically since each parity has conditional expectation zero, one or one half. Stop when all differences have been removed. The direction span W has at most 4s members (W={0} for s=1). In every coset x+W the restriction of g combines equal characters, and the isolated coefficient indexed by a₀|W remains c_a₀ times a sign. Distinct Walsh characters on W are linearly independent in odd characteristic, so every coset contains a support point.

Let D consist of W and all e_i+W. These at most 4(n+1)s shifts connect the support of g. Each coset's support is a clique under W, and any two support points from neighboring quotient cosets differ by e_i+w. The quotient cube is connected. A first support point is found by evaluating g on W.

## Decision and witness

If P(x₀)=b at that support point, return it. If P is constant reject. Otherwise a desired point exists exactly when some edge in the support graph has endpoints of different P values. For each shift v∈D form g_v(x)=g(x)g(x+v), with at most s² distinct coefficients by convolution, and P_v(x)=P(x)+P(x+v). All leading terms cancel, so degree drops by at least one. Ask recursively if P_v=1 at a point with g_v≠0. A positive recursive result gives two support points x,x+v of opposite P values; return the desired endpoint. Conversely any support path from x₀ to a desired point contains such an edge. Over a field nonvanishing of the product is equivalent to nonvanishing at both endpoints.

Depth is at most d. At level j each support size is at most s^{2^j}. Each step enumerates polynomially many shifts in the current support size and n, builds sparse convolutions and translates a Boolean polynomial with at most 2^d terms per input monomial. The resulting runtime is (n+s+input size)^{O_d(1)} including witness recovery.

## Fixed modular weights

For the odd p-group use its exact indicator g over F_p built by the truncated Lucas product in README.md. For each modulus 2^k of the 2-primary group use the same truncated product over F₂: its Boolean indicator has degree at most 2^k−1 after substituting the affine bit forms. The product of these indicators has fixed degree at most the sum of those bounds. Use P=1 as target. This permits arbitrary affine offsets and coordinates contributing to several group factors. Multiple distinct odd primes remain outside the argument.

The independent support_check.py implements small-instance checks comparing the recurrence with full truth tables. It uses exhaustive greedy-direction maximization in small dimensions, where the algorithm above uses conditional expectations.
