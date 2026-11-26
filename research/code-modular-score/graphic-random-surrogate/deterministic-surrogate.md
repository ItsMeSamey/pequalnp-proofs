# Deterministic star selection by simultaneously preserving connectivity

Use the same credited child components, actual edges, clique torso T on n bag vertices, bounded adhesion a≥2, C=binom(a,2), and desired surrogate vertex connectivity K≥1 as in README.md. Every credited child component can realize the star at any one of its ports. No bound is imposed on the number of port sets containing a bag vertex. Put
k=ceil(2aC(K+2)log_2(2n)).
If κ(T)≥K+2k, there is a deterministic algorithm polynomial in the input size for fixed a,K, constructing one root per component for which the simple surrogate J is K-connected.

## A rational choice of weights with small inclusion probabilities

For each Z⊂V(T) with |Z|<K the graph T−Z is 2k-edge-connected. Obtain k edge-disjoint spanning trees by graphic matroid union (a maximum independent set in the union of k graphic matroids decomposes into k forests, hence into trees at maximum possible size). Existence follows from the spanning tree packing theorem: every partition into h≥2 classes has at least kh crossing edges, by summing the lower bounds on their cuts. Let H be the union of the chosen trees, with m_H edges. [Nash-Williams, Edge-disjoint spanning trees](https://doi.org/10.1112/jlms/s1-36.1.445).

Start with all edge weights w_e=1 on H. Write τ(w) for its weighted spanning-tree sum and p_e for the probability that e belongs to the tree sampled with probability proportional to its edge product. While p_e>2/k for an edge, halve that weight. The potential
τ(w)/(∏_{e∈H}w_e)^{1/k}
is always at least one by the arithmetic-geometric mean inequality on the k packed tree weights. It starts at most 2^{m_H}. A halving multiplies this potential by (1−p_e/2)2^{1/k}, at most exp(−(1−ln 2)/k). Thus O(km_H) halvings suffice. The p_e are computable and comparable exactly by Laplacian cofactors, with denominator/numerator bit lengths polynomial in n and k.

Write b_e for a reduced incidence column, L=Σ w_e b_e b_e^T, and choose a real matrix Q with Q L Q^T=I (e.g. inverse Cholesky factor). Put U_e=w_e Q b_e b_e^T Q^T. Then Σ U_e=I and ||U_e||=w_e b_e^T L^{-1}b_e=p_e≤2/k, by the determinant derivative, the matrix-tree theorem and rank one. These matrices are separate for each Z. Their role is to certify connectivity of a selected subset of H, which is equivalent to positive definiteness of its sum of U_e.

## Simultaneous deterministic rounding

Use one matrix block for each Z, with dimension |V(T)−Z|−1. The total block dimension D is at most n^{K+1}. In every H designate actual edges as fixed and give each other edge e a single owner among credited components containing both of its endpoints. This designation can depend on Z. Let A0 be the block diagonal sum of all fixed U_e. If component i is rooted at a uniformly chosen port, let Y_i contain in block Z the U_e of its owned H edges for which that selected root is an endpoint. These edges are present in J−Z. Each is retained with probability ≥2/a even if other ports belong to Z, because its own endpoints survived. There are at most C owned edges per component in each block. Therefore 0≤Y_i≤R I with R=2C/k and
A0+Σ E[Y_i] ≥ (2/a)I.
Choices at different components are independent; a single choice determines all its blocks.

Put θ=1/R. For a prefix of fixed choices use
Φ=tr exp(−θ A0−θ Σ_chosen Y_i + Σ_unfixed log E exp(−θ Y_i)).
For one unset component, the average of Φ after selecting its port is at most the current Φ by concavity of X↦tr exp(H+log X) on positive definite matrices with H fixed Hermitian. Hence some choice never increases the exact estimator. [Tropp, Corollary 3.3 and Theorem 3.2](https://arxiv.org/pdf/1004.4389).

Bound the initial estimator using exp(−θY_i)≤I−(1−e^{-1})Y_i/R, the spectral chord inequality on [0,R]. The logarithm is operator-monotone and log(I−U)≤−U for 0≤U<I. Hence the exponent is bounded above by −(1−e^{-1})(A0+Σ E[Y_i])/R, so Φ_initial≤D exp(−(1−e^{-1})k/(aC))<1/4 with the stated k. At termination, if any block sum is singular then it contributes at least one to the trace of exp of its negative scaled matrix. Keeping Φ<1 thus certifies all the blocks positive definite and yields κ(J)≥K.

## Finite precision

If there are t credited components, it suffices to evaluate every candidate Φ to additive error 1/(16(t+1)). Selecting its approximate minimum increases the exact Φ by at most 1/(8(t+1)) over the best candidate. This leaves Φ_final<1 and does not need exact comparisons of transcendental values.

All matrix calculations can be done to this accuracy in deterministic polynomial bit complexity. Reduced L is rational and has smallest eigenvalue ≥min_e(w_e)/n², by restricting its quadratic form to a packed spanning tree whose reduced incidence inverse has entries in {0,1,−1}. Its maximum eigenvalue is polynomial and min_e(w_e)≥2^{-O(km_H)}. Construct Q by rational LDL^T elimination and square-root bisection with polynomially many guard bits; rational minors of L have polynomial bit lengths. Thus U_e can be approximated to any inverse-exponential precision with polynomial effort. Each exp(−θY_i) has spectrum in [e^{-1},1], as does its average inside a logarithm. Compute that logarithm by −Σ_{d≥1}(I−A)^d/d, a geometrically convergent series on a fixed interval bounded away from zero; compute the exponentials by Taylor expansion with polynomially many terms. The final exponent has operator norm polynomial in input size (≤θ+t for the remaining log terms plus θ times at most tR for the chosen terms). Taylor sums at polynomial norm, including intermediate amplification exp(poly), require only polynomially many binary guard bits for the stated inverse-polynomial absolute trace accuracy. Equivalently apply these calculations separately block by block with error divided by D. Symmetrizing numerical approximations preserves the Hermitian setup. An exact integer max-flow verification of the returned graph is available independently of the approximations.

This deterministic construction can replace the random step both with a supplied decomposition and in recognizable-component-torsos.md. In the latter case add C to the required original κ(T_X) for omission of the parent side and choose K as the physical-bag bound plus F C for the at most F exceptional children. The logarithmic dependence on bag size remains. These statements do not supply an arbitrary-host decision algorithm.
