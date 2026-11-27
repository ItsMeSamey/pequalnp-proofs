# A radius-three limitation on the vector-colouring Gram

On a sequence of growing-girth six-regular graphs assume a PSD matrix T having diagonal one, edge entry −1/2, one entry for each of distances two and three, and a common tail c beyond distance three. Values may vary across graphs. Write T=f(A)+cJ, since the distance matrices through three are I,A,A²−6I,A³−11A. The coefficients are uniformly bounded by the Gram entry bounds. Pass to convergent subsequences of c and the cubic coefficients. Positivity in the constant direction implies c≥0 in the limit. Orthogonal eigenvectors give f≥0 on the whole limiting spectral interval [−R,R], R=2√5, since McKay's limiting spectral measure μ has positive mass in every interior interval (https://doi.org/10.1016/0024-3795(81)90150-6).

Normalized traces give μ(f)=1−c and μ(xf)=−3−6c. In particular f is nonzero but μ((x+3)f)=−9c≤0. Any cubic of degree at most three nonnegative on [−R,R] is a sum of terms (R±x)(a+bx)². Indeed (1+t²)^3 f(R(1−t²)/(1+t²)) is globally nonnegative, hence a sum of real squares of degree at most three by factorization. Average at t and −t to separate even and odd squares, then substitute back.

Using μ(1)=1, μ(x²)=6, μ(x⁴)=66 and zero odd moments, the summands' contributions to μ((x+3)f) have quadratic matrices with diagonal entries 3R±6 and 18R±66, off-diagonal 6R±18. Both top diagonals and both determinants 432±90R are strictly positive. Thus the integral is positive, contradiction.

Consequently the specified radial constant-tail form is impossible for all sufficiently large girth at degree six. This does not give a quantitative girth threshold or exclude arbitrary simultaneous SA5 and PSD witnesses.
