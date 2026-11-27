# Adaptive affine branching cannot compress every quadratic leaf table

Suppose f on q bits has the directional property that on every affine space of dimension at least k and every nonzero shift its derivative is one on at least a γ fraction. Take any partition of the input cube into nonempty affine spaces W_i, including leaves of an adaptive parity decision tree. On W_i approximate f by a lookup table h_i of r_i quadratic features chosen specifically for that leaf. Both h_i and the features may depend arbitrarily on f. Define T=Σ_i 2^{r_i}, and let E be the total number of incorrect primary inputs.

With k≥1 write N_i=|W_i|=2^{n_i} and M_i=2^{r_i}. Then

    2^q ≤ 2^k T + (2√2/γ) E √T.

Identify W_i with GF(2)^{n_i} using an affine basis. Every nonzero tangent shift is a nonzero original shift, and a subspace in the leaf of dimension at least k remains such a subspace of the original domain. Quadratics restrict to quadratics. When r_i≤n_i−k, the companion collision calculation gives E_i≥(γ/2)sqrt(N_i²/M_i−N_i)≥(γ/(2√2))N_i/√M_i. Therefore N_i≤(2√2/γ)E_i√T. On the remaining leaves N_i≤2^k M_i, including those of dimension below k. Summing over disjoint leaves proves the inequality. [Collision inequality and primary extractor parameters](directional-quadratic-frontier.md)

For the explicit polynomial-time Li–Zhong extractor at k=ceil(c log₂ q) and constant γ>0, exact tabulation costs T≥2^{q−k}. Even with E≤poly(q), one has T≥(1−o(1))2^{q−k}: either T already exceeds 2^{q−k}, or E√T=o(2^q). The argument allows different feature maps on every leaf and arbitrary topology and basis choices. The work parameter charges one complete outer table per leaf. Memoization across leaves, sparse transforms, succinct suffix evaluation, deciding mere satisfiability, and nonlinear branching regions are different models. The extractor source gives polynomial-time evaluation and does not place the constructed function in Bq log q binary gates. [Li and Zhong, ICALP 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.108)
