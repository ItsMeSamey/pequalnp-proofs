# A one-sided principal-minor criterion for singleton guards

Work over GF(2). For a square matrix A and marker h, seek a vector x with hᵀx=1 and xᵢ(Ax)ᵢ=0 for every i. Constant guard offsets can be absorbed into the diagonal since xᵢ²=xᵢ.

Such a vector exists precisely when there are a nonempty principal index set S and i in S for which det A[S]=0 and det (A+eᵢhᵀ)[S]=1.

Take a marker-positive witness of minimum support S. Its restriction is the all-ones vector in ker A[S]. If the dimension of that kernel were at least two, it would contain a nonzero vector with marker zero. Adding this vector would yield a marker-positive kernel vector with strictly smaller support. Extending by zero is feasible for the original guards, a contradiction. Hence the kernel and left kernel are one-dimensional. Pick i where a nonzero left-kernel vector is nonzero. Any vector killed by the row-updated matrix must have marker zero, by multiplying by that left-kernel vector. It must then belong to the original kernel, where only the zero vector has marker zero. This proves invertibility of the updated matrix.

Conversely, any nonzero vector in ker A[S] has marker one when the updated matrix is invertible. Extend by zero to obtain a feasible witness. Thus the certificate supports ordinary Gaussian witness recovery.

The distinction between directed discrepancy and inequality is essential. With A=[1], h=[1], its single nonempty principal determinant changes from one to zero, but x=0 is the only feasible vector. A polynomial-time test of principal-minor equivalence does not on its own decide this directed test. Chatterjee, Ghosh, Gurjar and Raj give such an equivalence algorithm in [STOC 2025](https://www.cse.iitb.ac.in/~rgurjar/papers/PMESTOC25.pdf). This criterion does not establish a polynomial-time algorithm for the unrestricted nonsymmetric marker problem.

The Python checker enumerates all 4,164 matrix/marker pairs up to dimension three, plus 300 reproducible random pairs in dimensions four through eight.
