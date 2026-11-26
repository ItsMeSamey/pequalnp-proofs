# How much can clause-violation moments tell us about SAT?

For every n ≥ 3, two width-six CNFs on 3n variables and 32n clauses have identical moments of the number of violated clauses through degree n−1. One has exactly 2·4ⁿ satisfying assignments. The other is unsatisfiable.

## Construction

At each vertex of an n-cycle place three independent bits and set h(a,b,c) = a XOR (b AND c). For each edge i prescribe a sign sᵢ. The constraint requires hᵢ XOR hᵢ₊₁ = sᵢ. For each of the 32 forbidden local assignments, add the six-literal clause that excludes precisely that assignment. A violated edge contributes exactly one violated clause. Each variable occurs in 64 clauses. Compare the all-zero signing with a signing having exactly one nonzero edge.

Each bit value of h has four preimages. Given the vector of failed edges, choose the first hidden bit, then propagate around the cycle. Closure occurs precisely when the failure vector has the same parity as the signing. Every permitted vector therefore has exactly 2·4ⁿ preimages. Its restriction to any j<n edges is uniform, since each restriction has 2ⁿ⁻ʲ⁻¹ completions of the prescribed parity.

Writing V for the number of violated clauses, the binomial moment E[choose(V,j)] is choose(n,j)/2ʲ for j<n, by summing over j-element subsets of the edges. These polynomials span every polynomial of degree less than n. The degree-n binomial moment distinguishes the two signings. Here V counts all individual CNF clauses. Observing precisely which clauses fail gives more information.

## Affine preprocessing

The four words 000, 001, 010 and 111 in the h=0 fiber affinely span the whole three-dimensional Boolean cube over the two-element field. Flipping the first bit gives the other fiber. Each allowed edge relation contains a product of two full-span fibers, so it affinely spans all six input dimensions. Replacing each edge table by its affine hull loses the constraint. The nonlinear partition into the two fibers recovers an ordinary cycle parity test in linear time.

## Verification

The Python checker constructs actual clauses, evaluates their signed literals on every assignment for n = 3, 4, 5, verifies every proper edge marginal and every stated binomial moment, and checks affine ranks for both signs. Lean proves the path-fiber bijection and the parity criterion for satisfying the whole cycle. Its path numbering starts immediately after the omitted edge. The CNF encoding, fiber counts and affine-rank argument are given above. [Executable check](check.py) · [Lean development](../../lean/Research/CycleParity.lean)
