# Optimal additional marker count for quadratic-zero chart reductions

Under singleton guards x_i(Mx)_i=0 and consistent markers Hx=h, every witness has q=xᵀMx=0. By ../slice-normalize/README.md a subflat permits a globally alternating equivalent row normalization exactly when q vanishes there. Let 2r be the polar rank of q restricted to the marker slice. Symplectic Gaussian elimination puts this restricted q into one of the following normal forms, with irrelevant radical coordinates free.

- Balanced q=a·b+u uses a fresh radical coordinate. Fix a and impose u=a·b, partitioning the zeros into 2^r flats of codimension r+1.
- Minority zeros q=a·b+1: fix each nonzero a and impose a·b=1, partitioning the zeros into 2^r−1 flats of codimension r+1.
- Majority zeros q=a·b: identify the a-space with GF(2^r) and the b-space with its binary dual. For each field t take the graph b=B_t(a,·), where B_t(a,x)=Tr(t(a x²+a²x)) is alternating bilinear. At nonzero a the kernel of x↦a x²+a²x is {0,a}. Nondegeneracy of the trace pairing implies the B_t(a,·) fill every b annihilating a. Add the flat a=0. These at most 2^r+1 flats all have codimension r. Constant zero takes just the full slice and constant one rejects.

By the scalar quadratic flat formula in ../compression/fiber/README.md those codimensions are the least possible through every zero point. For b original markers this reduces to at most 2^r+1 alternating instances with b+r or b+r+1 affine markers, with 2^{O(r)} polynomial preprocessing. The majority cover size is only an upper bound. The chart budget is optimal for this method and does not establish a general solver at unbounded marker count.
