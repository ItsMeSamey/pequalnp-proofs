# Decision-preserving real replacements

## Nonnegative matching kernels under pins

Let K be a fixed nonnegative real matrix on two copies of the Boolean cube of dimension m≥1. Its sum on a product of pinned subcubes is the scheme's scalar answer. Suppose one common threshold τ>0 distinguishes satisfiable equality constraints x=y (scalar ≥τ) from unsatisfiable restrictions (scalar <τ). Then rank(K) ≥ 2^m−2m+1.

For each z the diagonal Kzz is at least τ by pinning all coordinates. For each i and each bit a, pin x_i=a and y_i=1−a while leaving every other coordinate free. The sum on this rectangle is less than τ. The 2m pinned rectangles cover all off-diagonal entries. Nonnegativity gives total off-diagonal mass <2mτ. Fewer than 2m rows have off-diagonal sum at least τ. Retain the other rows and their corresponding columns. Each diagonal exceeds its row's off-diagonal sum. The resulting square submatrix is invertible, as seen by applying a putative null vector's largest-magnitude coordinate to its row equation. This gives the stated rank bound. If all no cases have scalar zero, positivity immediately gives rank exactly 2^m. For an absolute count approximation with error <1/2, the common threshold 1/2 applies.

The argument transfers to a cut where fixing all other variables isolates m equality constraints across the cut and the fixed kernel is reusable under unary pinning. Independent equality constraints alone have a fast decision algorithm. This theorem concerns a fixed nonnegative scalar model, and signed interpolation or refitting the representation after each query can evade its hypotheses.

## Amplification in square Hermite reconstruction

For nodes 1,…,Q and jets of multiplicity J, the unique square Hermite interpolation row evaluating a degree <QJ polynomial at zero assigns weight of magnitude t^(J−1) binom(Q,t)^J to the highest jet at t. Indeed, its cardinal polynomial is (T−t)^(J−1) times the J-th power of the Lagrange cardinal polynomial for t. It has the required local coefficient at t, all lower local coefficients zero, and zeros of multiplicity J at every other node. The Lagrange cardinal polynomial has magnitude binom(Q,t) at zero. Perturbing only this jet therefore realizes the specified amplification. A uniform independent error box needs radius less than 1/(2 times the weight) to promise absolute error <1/2. More generally its exact worst-case error is radius times the sum of absolute weights. Lower known degree, structured errors, exact rational computation and a different reconstruction require separate analysis. The logarithm of this amplification is polynomial for polynomial Q,J.

## Bounded-coefficient robustness of a determinant obstruction

Let B(T) be an m by m real polynomial matrix of entry degree ≤R with B(0)=I. At node t write B(t)=A_t+E_t, rank(A_t)≤m−k_t. Bound the Euclidean norm of every row of E_t by δ≤1, and the row norms of A_t and every positive Hasse jet of B there by M≥1. If the sum of k_t exceeds mR, choose local multiplicities n_t≤k_t summing to mR+1. Let L be the sum of absolute weights for evaluating at zero by the corresponding Hermite formula. Then

    δ ≥ 1 / (L (R+2)^m M^m).

To see this, expand det B(t+u) by multilinearity in its rows. Each row is taken from A_t, E_t or one of R positive Taylor coefficients. A nonzero determinant summand uses at least k_t rows outside A_t. A term of degree j<k_t uses at most j positive-degree rows, hence at least k_t−j rows of E_t. Hadamard's inequality bounds each such determinant by δ M^m, and there are at most (R+2)^m choices. All local determinant jets requested by the formula obey (R+2)^m δ M^m. The interpolated value is det B(0)=1. The inequality follows.

The bound applies when the exact-layout argument supplies a square witness with excess deficiency and an approximate layout supplies low-rank matrix approximations to it. It is a precision threshold conditional on row bounds. It does not rule out coarse perturbations preserving the particular Boolean decision, unbounded coefficients, or signed low-rank decision schemes.

## Perturbing the restored Boolean occurrence directly

Suppose that at the origin every occurrence evaluates within δ of the true assigned bit, with perturbed values in [0,1], and clause factors are their multilinear Boolean extensions. The clause value is the expectation of its truth predicate under independent bits of the supplied means. Coupling these bits to the original Boolean inputs bounds the factor change by its arity times δ. Since all factors are in [0,1], telescoping products gives total absolute count error at most 2^n Mδ for M variable occurrences. In particular δ<1/(2^(n+1) M) guarantees rounding.

Exponential dependence on n is necessary for worst-case unnormalized scalar summation in this model. On n variables take factors x_1 and 1−x_1 with n−1 free variables. Replace the input in both occurrences by (1−δ)x_1, a homogeneous linear replacement. The true count is zero but the perturbed total equals 2^(n−1)δ(1−δ). For δ≤1/2 this is at least 2^(n−2)δ. A decision based on strict positivity fails for every 0<δ<1. A threshold of 1/2 fails for δ≥2^(1−n) whenever δ≤1/2. This is a worst-case example for raw summation. Simplifying the contradictory clauses first would solve this example, so it gives no general algorithmic lower bound.

## Constant assignment-wise error at the origin preserves the exact rank barrier

Suppose the nonzero-node low-rank/layout conditions still hold exactly and every replacement at zero satisfies |<p−e_v,x>|≤δ for every Boolean assignment x, for δ<1/2. The Boolean indicator of the positive coefficient set and that of the negative coefficient set give respectively at most δ total positive mass and δ total absolute negative mass. Hence ||p−e_v||_1 ≤2δ<1. Every selected square submatrix B(0) in the determinant layout proof consequently satisfies ||B(0)−I||_infinity<1 and is invertible. The original root-multiplicity proof goes through verbatim because it uses only det B(0)≠0. In particular, even constant-small restoration error with exact layouts cannot circumvent the field-independent degree/rank bound over the reals. This assumption is assignment-wise and stronger than correctness of the final scalar decision. In the preceding precision threshold for approximate special-point ranks, the left side det B(0)=1 can likewise be replaced by |det B(0)|≥(1−2δ)^m, since all eigenvalues of B(0)−I have magnitude ≤2δ.
