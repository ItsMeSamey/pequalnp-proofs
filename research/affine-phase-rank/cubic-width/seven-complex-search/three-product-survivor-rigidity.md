# Three product survivors leave at most one entangled fourth ray for G₂

Fix three product stabilizer rays on the two original blocks. There is at most one choice of their weighted contributions and an entangled stabilizer tensor E summing to the fixed target g⊗g. This concerns a decomposition of length four, with no zero terms or coefficient restrictions. Entangled examples exist.

**Structure.** Let r be the Schmidt rank of E. For r=8, subtracting the rank-one target still has rank at least seven. For r=4 or 2, the target lies outside its respective proper row and column stabilizer codes, so their difference has rank r+1. Only r=2 is possible given the three products. Their local triples are independent on both sides, and their local three-spaces are span(g,C) where C is the corresponding two-dimensional Schmidt code. In those local bases write g's coordinates x and y. Absorb the three product coefficients into a nonsingular diagonal matrix D. The coordinate matrix of E is xyᵀ−D. Since its rank is two, yᵀD^{-1}x=1, and its column space is ker(yᵀD^{-1}); similarly its row space annihilates D^{-1}x. A left endpoint at index i is in its code exactly when y_i=0. A right endpoint is in its code exactly when x_i=0.

On each side the exterior stabilizer types alone miss g by the local three-space certificate (single-bell-ghz-exclusions.md). Thus for some index x_i≠0 and y_i=0, and for another y_j≠0 and x_j=0. Both vectors need at least two coordinates to represent a nonstabilizer, so after indexing their supports are {1,3} and {2,3}, respectively. These labels are determined by the two triples. The product pairs are (a,f),(e,b),(p,q), where a,b are in the respective codes, (a,p) and (b,q) are the physical CCZ secants, and e,f are exterior rays distinct from the respective partners p,q.

Fix the unique weighted secant gauges g=a+p=b+q. Modulo the appropriate local qubit code, both exterior rays in each three-space have nonzero proportional images. Normalize e to p and f to q in those quotients. Projecting the decomposition on the left quotient forces both the (e,b) and (p,q) coefficients to be one, since b,q are independent. The right quotient likewise forces coefficient one on (a,f). Thus
E=a⊗b−(e−p)⊗b−a⊗(f−q).
Put u=e−p, v=f−q, both in their respective local codes. If u=c a+u_perp and v=d b+v_perp are orthogonal decompositions, the rank-two logical stabilizer is maximally entangled. Its coefficient matrix in local orthonormal bases beginning with the directions of a and b has vanishing bottom-right entry, forcing the top-left entry to vanish and the other two to have the same magnitude. Hence c+d=1 and ‖u_perp‖²/‖a‖²=‖v_perp‖²/‖b‖².

**Finite local verification.** The fifteen CCZ secants are the seven complementary-plane pairs and the eight point-mass/full-chirp pairs (local-code-secants.md). Affine input changes preserve g after correction by a quadratic sign, and act transitively on points and on affine planes; the cubic top coefficient is invariant under invertible three-bit changes. Thus each oriented choice has one of three representative inside types. For each, there are exactly seven encoded-qubit codes C containing it, corresponding to two-dimensional subgroups of its three-dimensional stabilizer label group, with forced signs. For each code the companion checker filters the 1080 local stabilizer rays for the additional exterior e with quotient proportional to p and with a,e,p independent. It computes c and the relative squared norm above and checks that each qualifying e occurs in just one C. Its results are:

| Inside endpoint | Number of (C,e) choices for representative | c | Relative squared norm |
|---|---:|---:|---:|
| Plane | 4 | 0 | 1 |
| Point | 7 | 1 | 1 |
| Full chirp | 7 | 1/2 | 1/4 |

The code uses four times the code projector, computed from two signed commuting generators. Quotients and membership are checked by Gaussian integer cross-multiplication. Their entries come from eight amplitudes, Pauli signed permutations, and sums of at most four Pauli operators; the complex-array integer computations are exactly representable (all intermediate absolute components below 2^32). The final ratios use rational arithmetic. Checker: check-three-product-survivors.py, SHA-256 5eabb609668b57e1eab13a8fd00f05b5c99fb27bdbdf4ea2641c5ebbde913e0a.

Thus only a plane and a point in either order, or two full chirps, can be inside endpoints on the two sides. More importantly, the extra exterior ray of the supplied triple determines its only possible local code on either side. Both quotient scalings and E are then fixed exactly. The table gives necessary conditions; testing whether the unique resulting residual is a stabilizer ray decides the fixed triple.

**Example and physical consequence.** Let δ mark point 111, H indicate the affine plane z=1 and e=H−2δ. Then g=1−2δ and
g⊗g=1⊗e+e⊗1+4δ⊗δ+1[z₁=z₂](−1)^{z₁}.
The last tensor is an entangled stabilizer of Schmidt rank two, and the other three are stabilizer products.

In a three-ordinary, four-exceptional physical seven-list, a local stabilizer bra which retains g, erases three exceptions, and leaves the fourth exceptional image entangled must preserve all three ordinary terms. For a fixed measured party their remote rays are fixed. Consequently every such bra produces the same normalized weighted three product contributions and the same normalized weighted entangled residual, even when it isolates a different exceptional ray. The normalization divides the output by the nonzero local contraction of g. This does not assume any such bra exists.
