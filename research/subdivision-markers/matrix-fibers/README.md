# Largest flats in a full-row-rank matrix-product fiber

Fix n,s >= r, X in F2^(n by r), Y in F2^(n by s) and B in F2^(r by s) of rank r. Write g(r) for the maximum dimension of an affine subspace of invertible r by r matrices on which inversion is affine. Every solution (X0,Y0) of X^T Y=B lies on a largest solution flat of dimension s(n-r)+g(r).

For the upper bound take any solution flat through (X0,Y0) and let P be its affine projection to X. Let D be the span of all columns occurring in matrices of P, of dimension d. The direction kernel over each X consists of common Y-directions K satisfying X^T K=0 for every X in P (simply compare solutions in the same Y-fiber). Thus its dimension is at most s(n-d). The image projection of P on matrices with columns in D/col(X0) has dimension at most r(d-r), since X0 has column rank r. Its fiber through X0 consists precisely of a family X0 T with T in an affine space F containing I. Each T is invertible since X0 T has column rank r. Select a linear right inverse of the projection of the flat's directions to the X directions along this fiber. It gives an affine lift Y(T) within the flat. Then X0^T Y(T)=T^(-T) B. Multiplying by a fixed right inverse of B proves inverse transposition, hence inversion, is affine on F. Thus dim P <= r(d-r)+g(r), and the flat dimension is at most s(n-r)+g(r)-(s-r)(d-r).

For attainment normalize any maximizing family to contain I by left multiplying by the inverse of one member. Inversion remains affine. Fix a right inverse J of X0^T. For all T in that family take X=X0 T and

    Y=Y0 + J(T^(-T) B - B) + K,

where K ranges over matrices with columns in ker(X0^T). This is an affine injectively parametrized solution family through (X0,Y0) of the asserted dimension.

## The value g(3)=2

Every invertible 3 by 3 binary matrix has determinant one, so its inverse is its adjugate. Each 2 by 2 minor must therefore restrict to an affine function on a feasible family. Consequently its bilinear polarization vanishes on every pair of directions. Independent invertible transformations on the left and right preserve this statement (equivalently, they preserve inversion affineness on the transformed family).

If a direction has rank three, transform it to I. Polarizing with I in the principal 2 by 2 minors forces all three diagonal entries of each direction M equal. For i different from j and the third index k, the minor on rows i,k and columns j,k forces M_ij=0. Thus there is at most one dimension.

If a direction has rank two, transform it to diag(1,1,0). Polarizing against it in the minors containing the first or second diagonal pivot forces M_13, M_23, M_31, M_32, M_33 all zero (and M_11=M_22). Every direction therefore lies in the top-left 2 by 2 matrix block. Polarization of its determinant gives a nondegenerate alternating pairing on its four entries: the diagonal entries pair with each other, as do the off-diagonal entries. The direction space is isotropic, of dimension at most two.

Otherwise all nonzero directions have rank one. Such a space has either a common column line or a common row line. Indeed the sum of two rank-one matrices has rank two whenever both factors differ in each position. If two matrices share their left factor and have different right factors, any third must have the same left factor to be compatible with both; swap sides in the other case. In dimension three the space would contain every x f^T for one fixed nonzero f (or their transposes). Its translate by an invertible A contains a singular matrix: choose z with f^T z=1 and put x=Az. Then (A+x f^T)z=0. No three-dimensional family is feasible.

The matrices I+e1 w^T with w_1=0 form a two-dimensional affine family, each its own inverse. More generally, all matrices I+N with N supported in the upper-right p by (r-p) rectangle are their own inverse. This gives g(r)>=floor(r²/4) for all r.

The independent matrix_check.py enumerates every binary matrix through size three, calculates actual inverses using elimination, and grows precisely the linear spaces of directions on which the translated inverse map is linear. Left translation normalizes any affine family at I. Counts by increasing dimension are [1], [1,5], and [1,167,35] for r=1,2,3. The enumeration confirms g(1)=0, g(2)=1 and g(3)=2.

## Rank four and optimal covers for ranks up to four

Two independent exhaustive enumerations give g(4)=4. Every normalized maximizer has direction space {A : im A⊆U⊆ker A} for a two-dimensional U, giving exactly 35. The certificate and programs are in g4-census/. The normalized counts in dimensions one through four are 20,159, 21,035, 2,795 and 35.

For each r≤4 the square-zero rectangular directions U attain g(r)=floor(r²/4), and I+U is a multiplicative subgroup. Hold one r-dimensional column space fixed and partition its ordered bases, identified with GL_r, into cosets of this subgroup. Each coset gives one maximum solution flat by the inverse-lift construction, and their X projections are disjoint. Varying the column space covers the complete solution relation. Counting ordered full-rank X and the size of their Y fibers gives the exact minimum number of affine flats in any cover:

    (∏_{j=0}^{r−1}(2^n−2^j)) / 2^floor(r²/4).

For s>r the strict loss unless d=r forces any maximum flat through a point to fix col X. It then contains the complete Y kernel and is determined by one normalized inverse-affine maximizer after identifying X at this point with I. Thus there are exactly 35 maximum flats per point for r=3 or r=4 in that range. No such classification is asserted for s=r.

The ambient codimension rn+rs−g(r) lower-bounds native guarded terminal count for any representation preserving the exact observed solution relation. The circuits-to-guards conversion consequently gives at least rn+rs−g(r)−1 AND gates in any XOR/affine/AND circuit for the relation; this lower bound need not be attained.
