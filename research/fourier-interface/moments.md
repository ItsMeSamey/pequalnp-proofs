# Replacing the integer-fiber loop by polynomial moments

## The weighted sum in the rational interpolation program

Fix a manuscript node t and one finite-difference pair U subset E. This note addresses the rational interpolation algorithm (in particular its group-sum identity), not the separate headline tensor algorithm. At this stage the coefficient algebra is a commutative rational algebra, including the actual jet algebra Q[z,V]/(z^J,V^ell). The groups contain independent Boolean assignments x_g subject only to local pins. Cx concatenates integer measurements from these groups. Local weights incorporate the deformed factors. Write

    Z = sum_x product_g f_g(x_g,Cx).

This polynomial form is valid in the actual program. For each group solve C_h R_h y=y on im(C_h) over the rationals and extend R_h linearly to all coordinates. Kernel invariance of the zeroth-order replacement rows lets R_h y replace an external Boolean representative. Fixed U supplies the higher-order differences independently of x. Therefore f_g(x_g,Y) is a computable polynomial in formal measurements Y and is correct at Y=Cx; it need not be a weight at an attainable Boolean assignment when evaluated elsewhere. The product's total Y degree is at most d=k(m_test+2(ell-1)) in the sparse-system application by the manuscript's total-order lemma in the V-truncated algebra. The simpler fixed-width sparse clause application has degree bounded by its total factor degree. Higher-order jets and rational or signed entries are allowed.

## Finite-difference moment algorithm

Let c be the number of rows of C and let Δ be a known downward-closed set containing the Y-monomial support of F_x(Y)=product_g f_g(x_g,Y), for every x. Use Δ={alpha: |alpha|<=d} when only the total degree is known. Let B=|Δ|; in the total-degree case B=binom(c+d,d). A standard explicitly iterable Δ or the total-degree simplex suffices in the streaming bound. All factorials, powers of -1, and binomial coefficients for multiindices are coordinatewise products, with signs equivalently given by total order parity.

Newton's forward-difference formula gives

    F_x(Cx) = sum_{alpha in Δ} sum_{beta<=alpha}
       (-1)^|alpha-beta| binom(alpha,beta) F_x(beta) binom(Cx,alpha).

This identity holds at negative integer coordinates as a polynomial identity. To compute the alpha,beta sum over x, put a=|alpha|. For each gamma<=alpha evaluate in the single fresh jet variable s modulo s^(a+1),

    K_gamma(s)=sum_x F_x(beta) product_i (1+s gamma_i)^((Cx)_i).

Compute K as a product of group sums. A variable j contributes unary weight product_i (1+s gamma_i)^(C_ij) when x_j=1 and one otherwise. Negative exponents use the truncated generalized binomial series. Thus all exact integer constraints disappear from the local subroutine; bit pins remain. Crucially, multiply all group sums in the common jet ring before extracting [s^a].

The coefficient [s^a]K_gamma is a homogeneous degree-a polynomial in gamma. Its gamma^alpha coefficient is exactly sum_x F_x(beta) binom(Cx,alpha). By mixed forward differences that coefficient is

    (1/alpha!) sum_{gamma<=alpha} (-1)^|alpha-gamma| binom(alpha,gamma) [s^a]K_gamma.

To see this, any monomial of total degree a survives the alpha-th difference only if its exponent vector dominates alpha, hence equals alpha. This proves the evaluation algorithm. There are at most B^3 triples (alpha,beta,gamma), since each sub-box of a point of Δ lies within Δ. The black-box cost is B^3 times polynomial overhead and the largest cost of evaluating a single sum of group weights with unary jets; brute force costs a polynomial times sum_g 2^|S_g|. Tuple-value ranges do not enter this exponent. For the manuscript's c<=2 tau n and d=O(n), log B=O(tau n log(1+1/tau)). For small d relative to c the symmetric bound O(d log(1+c/d)) applies (with constant-order terms). Zero rows and zero degree give the natural trivial cases.

Working space is polynomial in the actual input for the total-degree simplex: stream the three multiindices and the original one-group sums. Store only one univariate jet of order at most d in addition to the manuscript's jets. At grid arguments <=d, generalized binomials have O(d(log(2+d)+log(2+max |(Cx)_i|))) bits. All denominator changes from alpha! divide d!; the right inverses use pivot minors of polynomial bit length by Hadamard, with a single common denominator formed by multiplying polynomially many such pivot denominators. Power it to the polynomial total degree and multiply by the manuscript's previous common denominator. Each signed accumulation multiplies its magnitude by at most B^3 times the relevant binomial factors. In particular log B contributes only polynomially many bits. The same storage assertion for an arbitrary Δ requires a polynomial-space iterator and a polynomial bound on its maximum total degree and input coefficient sizes.

## What this permits for an inner solver

If after substituting formal measurements at a grid point the local factors read only a fixed number of original Boolean coordinates each and have bounded total density, a sparse weighted counting algorithm over a commutative rational algebra applies directly to the group, with the extra unary jets from the algorithm above. No Boolean wires for the measurements or Hasse coefficients are needed. One may absorb further dense linear directions into Y before applying the method. Given a proposed common row space L, test whether a row differs from some element of L on at most w coordinates by enumerating supports of cardinality <=w and solving linear equations. For fixed w this is polynomial. A fixed number of inputs to a factor, each with such a residual support, gives a fixed scope; the factors and total product must have the promised measurement-degree bound and evaluability. This gives an actual recursive use on checkable favorable inputs. Finding a useful common space for arbitrary instances is a separate issue. In the specific swap construction the opposite cross-block can have full rank even on a large physical fiber (see orbits.md).

For a pointwise universal separated representation, the corresponding exponential moment pairing has matrix diag(alpha!) in the monomial bases indexed by the total-degree simplex; its rank is B. This gives a B-term lower bound for representing that universal bilinear pairing by rank-one terms, without implying that scalar input-specific summation takes B steps. At the paper's published parameter settings, substituting the improved measurement cost leaves the Taylor and group terms of order n(log log n)^2/sqrt(log n). Under the same layout certificates Q log r=O(log n) and sufficient tail constraint R^2/Q=Omega(log(r/tau)), improving the overall order would require r much larger than sqrt(log n)/(log log n)^2. Then log r=Omega(log log n), Q=O(log n/log log n), and R/Q=Omega(log log n/sqrt(log n)), so the Taylor term (R/Q)log(2Q/R) prevents such improvement within that certificate. The sharp tensor theorem uses a different algorithm.

A central Hamming-weight equality on an even number s of bits illustrates why literal Walsh characters are a poor direct substitute for integer measurements: it has all 2^(s-1) even-index Fourier coefficients nonzero, since the middle-slice coefficient at weight k is proportional to [z^k](1-z^2)^(s/2) divided by binom(s,k). Fourier filtering with s+1 complex roots of unity succeeds for this single integer statistic. The moment approach instead uses integer grid evaluations and the actual degree of the downstream dependence.

* [OpenAI, group-sum identity, Hasse step, total-order degree and the numerical layout](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex)
* [Subexponential Weighted Counting and Exact Optimisation, author-deposited code and manuscript](https://zenodo.org/records/23718560)

The accompanying test checks eighty signed two-block instances, with negative measurement entries, Boolean pins, negative and rational weights and their first Hasse coefficients against exhaustive summation. The proofs give the symbolic guarantee.
