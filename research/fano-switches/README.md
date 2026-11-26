# Graph switches preserving every guard on a marker fiber

Let L have full row rank t over GF(2), and prescribe Lx=z. Delete any coordinate identically zero on this fiber, restrict the matrix to the remaining coordinates, and row-reduce the marker system again. Write l_i for column i of L.

**Exact switch space.** A symmetric matrix D satisfies x_i(Dx)_i=0 for every i and every x on the fiber if and only if

    D = Lᵀ K L + diag(Lᵀ K z)

for a symmetric t-by-t matrix K. Consequently adding D to a symmetric guard matrix preserves each indexed guard value on the entire fiber. This characterizes equality of the individual guard polynomials on the fiber. Preserving just their common zero set can allow other changes.

For necessity, each secondary slice Lx=z, x_i=1 is nonempty. A row vanishing there is in the span of the equations' normals, with the same linear combination of right-hand sides equal to zero. Hence D_i = b_i L + (b_i z)e_iᵀ. Stack the b_i into B. The matrix BL is symmetric because it differs from D by a diagonal. Since L has full row rank, col(B)=col(BL); symmetry places this space inside col(Lᵀ). Thus B=LᵀK for some K, and symmetry of LᵀKL implies symmetry of K by multiplying by a right inverse of L and its transpose. Conversely, on the fiber the i-th product of the displayed D is x_i(l_iᵀKz)(1+x_i)=0.

For a switch between simple graphs D must also have zero diagonal. In characteristic two lᵀKl=diag(K)ᵀl, so the exact additional condition is diag(K)=Kz. For nonzero z, in coordinates with z the last unit vector this equates each of the first t−1 diagonal entries with a distinct last-column entry and the last equation is automatic. Under a marker basis change the equation transforms covariantly because the diagonal of a symmetric form is a linear functional. For t=3 there are therefore 16 eligible K, possibly defining fewer distinct graphs. For z=0 there are eight.

**Solver for a recognizable class.** For each eligible K toggle off-diagonal edges according to l_iᵀKl_j. Find the connected components. If the columns in each component span at most two dimensions, choose coordinates on each local span, apply the [alternating two-marker algorithm](../two-markers/README.md) to each of its at most four outputs, and combine the attainable vectors over components by XOR. Any recovered support at z is feasible in the original graph. If every switch has a component of rank three the test reports that it did not recognize the input. For fixed t=3 this takes polynomial time and accepts arbitrarily large components with unrestricted adjacency inside a rank-two block. This is a sufficient recognition condition. The switch-space characterization itself requires no decomposition. The solver also works on rank-deficient inputs or with forced zero coordinates, although the described preprocessing is required for the completeness claim about the switch space.

Run `python -B check.py`. The [checker](check.py) compared the full switch set with every alternating perturbation in 226 small instances and compared every recognized decision and witness with exhaustive assignments in 134 additional instances.
