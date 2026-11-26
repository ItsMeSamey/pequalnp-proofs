# Fast swap-orbit evaluation and a full-rank cut inside a fixed measurement fiber

This analyzes the actual rational swap matrix, not the headline tensor-contraction algorithm. Statements about fully occupied copies are examples of valid layouts. They do not prescribe or lower-bound every execution of the deterministic label-selection procedure. The final obstruction concerns recovery of the entire specified vector of local port values, not scalar summation.

## Simultaneous fast evaluation

The auxiliary slots split into swap orbits. An orbit with b asymmetric positions is a Boolean group of order 2^b; the remaining symmetric positions have trivial swaps. Write X_i for the translations in these b positions. They commute with X_i^2=1. In this group algebra, the aligned operator obtained from M0 by removing its full swap V0 has Walsh symbol given on signs by

    f(w)=(-1)^A sum_{h=0}^{R-1} (-2)^h binom(w-A,h),
    w = number of negative signs.

Let m_J be the Fourier coefficients of this function, so the aligned convolution is sum_J m_J X_J. After freezing the shared correction (I-M0)x, the canonical local linear operator at T=t has coefficients

    m_J product_{s in J}(1-t/s).

In fact J is the set of positions left unswapped by the original, unaligned M0 transition and thus exactly the mismatch set appearing in the manuscript's coefficient correction. The term vanishes whenever t belongs to J. The remaining transfer stays in the assigned group after the alignment. These identities hold before the Boolean incidence embedding; embedding adds common columns or zeroes unused ones. All rows in an orbit may be applied at once in O(b 2^b) arithmetic operations using forward and inverse Walsh transforms and the precomputed multiplier. Damping can likewise be applied to polynomial jets. Summed over auxiliary copies, the runtime to transform a single assignment is O(Q M) arithmetic operations with precomputed constants when the total number of physical incidences is M and the occupied-plus-unused capacity is at most 2M. Constructing or transforming multipliers has a similar batched cost per distinct orbit type if not already available. This is an arithmetic evaluation cost, not the model count of a Boolean circuit of comparable size.

## A nonsingular cross-block

At t=1 assume the orbit is asymmetric at axis 1. Put a_s=1-1/s. Then a_1=0 and 0<a_s<1 at all other asymmetric axes. Delete axis 1 after fixing the common source/aligned-output half. On j other axes demand that the input lie in one subcube and the aligned output in the opposite one. Choose j=1 for even R, j=2 for odd R, with R>=j+1 and b>=R. The resulting square transfer on the remaining q=b-j-1 axes has dimension m=2^q and is nonsingular over Q.

For a remaining sign vector epsilon, sample independent random signs of means a_s epsilon_s. These distributions have full support. Let W count their negatives. The corresponding cross-block Walsh eigenvalue is

    (product of a_s on the j axes) (-1)^j 2^(-j)
    times (-1)^A (-2)^(R-1) E[binom(W-A,R-1-j)].

To derive this, multilinearly interpolate the original Fourier symbol in signs. Setting its first coordinate to zero averages f(w), f(w+1). Their mean equals (-1)^A(-2)^(R-1)binom(w-A,R-1), by Pascal's identity. Keeping only transitions with all j selected comparison axes flipped extracts their multilinear coefficient, equivalently taking j signed binary averages. Each contributes -1/2 times a forward difference, and a forward difference lowers the bottom binomial index by one. Finally evaluating the free coordinates at their damped signs gives the expectation. The remaining bottom index is nonnegative and even. The generalized binomial at an integer is then nonnegative. It is strictly positive somewhere on 0,...,q: if A>0 take W=0; if A=0 take W>=R-1-j (available since b>=R). Hence every eigenvalue is nonzero. The formula covers zero bottom index as well.

With a fully occupied orbit and distinct Boolean variables in its slots, this is a literal port-to-variable matrix. The sparse-scope premise of the weighted inner SAT algorithm already fails if R grows: on a full orbit, for any J excluding 1 of size R-1, the top-degree monomial m_J=(-1)^A. This follows from the leading term of f and the R-1 distinct swap choices. The canonical t=1 coefficient is nonzero on all these slots; the literal (unfrozen) polynomial row coefficient is m_J times (product_{s in J}a_s - 1), also nonzero for R>=2. Thus a single originally unary factor can take non-Boolean rational values at legitimate assignments. The cross-block theorem strengthens this syntax observation to full ordinary rank.

## Fixing every actual measurement

On this orbit the auxiliary exceptional rows are the Walsh characters whose total negative-axis count is outside I=[A,A+R-1]; symmetric axes add no negative signs. On the source subcube fixed in j+1 coordinates, each restricted character is a signed copy of a free-axis Walsh character. A free-axis character of weight l lies in the kernel of ALL restricted exceptional rows exactly when

    [l,l+j+1] is a subset of I.

Their span has dimension k equal to the sum of binom(q,l) over these weights; the actual restricted row rank is m-k. Every such character vector chi also supplies two actual Boolean inputs, (1+chi)/2 and (1-chi)/2 on the subcube with all other inputs zero, having identical measurements. Their differences span that kernel. On any common measurement fiber the frozen correction is constant, so injection of the canonical cross-block transfers to the literal output vector there.

There is a stronger counting consequence that permits arbitrary nonlinear encodings of port values. Select a basis of the restricted rows from the original integer rows. Each row is signed 0/1 and has at most 2m+1 possible values on the source cube. Therefore one fixed attainable fiber contains at least 2^m/(2m+1)^(m-k) inputs. The output vector on the opposite subcube distinguishes all of them, by nonsingularity. If (m-k)/m=o(1/q), this is 2^((1-o(1))m) distinguishable states on one actual fiber.

For the manuscript's published lambda=ceil(log2 n), nu=ceil(log2 lambda), Q=floor(lambda/(128nu)), R=(beta+3)ceil(sqrt(lambda)), mu=Q(r-1)/(2r), and A=floor(mu-(R-1)/2), take any orbit with its b within R/16 of 2mu and asymmetric at axis 1. For X binomial(q,1/2), the discarded fraction (m-k)/m is at most Pr[|X-q/2|>R/8] for sufficiently large n: all fixed axis offsets total at most three and the two interval centers differ by at most R/32+O(1). Hoeffding bounds this by 2 exp(-R^2/(32Q)), which is o(1/Q) at the published constants. Thus the information bound applies on each such orbit.

For a valid saturated layout of n distinct unit factors give every physical occurrence its own Boolean variable and fill entire auxiliary copies, discarding a last partial copy with o(n) slots for the lower-bound estimate. Full copies have uniform ordered label pairs and satisfy the balance certificate; the partial copy can be filled evenly (or simply omitted when choosing sizes) to keep all groups <=2n/r. In one group at node 1, a fraction 1-1/r of slots have an asymmetric first pair; conditional on these labels, the remaining asymmetry count is binomial(Q-1,1-1/r). Hoeffding and R^2/Q -> infinity show that all but o(1) of this mass has |b-2mu|<=R/16. In each such orbit exactly a 2^-j fraction of its slots in this group belong to the chosen source subcube. Hence their combined number is Theta(n/r). With disjoint variables and orbits, intersect the independent large measurement fibers and vary their source configurations simultaneously. The matching opposite-subcube output vectors distinguish 2^Omega(n/r) configurations. A scheme that explicitly enumerates distinct complete output-port states for this cut therefore has that many states. A scalar algorithm may sum implicitly or ignore most of the ports; indeed the chosen unit instance itself is easy.

[OpenAI's swap geometry, interpolation coefficients, incidence embedding and parameter proof](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex) are the primary definitions. The adjacent exact test constructs the raw Walsh coefficients and independently checks 1,054 rational cross-block eigenvalues and restricted-kernel dimensions across 75 small configurations. No asymptotic conclusion is inferred from those tests alone.
