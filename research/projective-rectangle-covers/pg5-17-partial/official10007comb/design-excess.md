# Excess multiplicity for the nonincidences of a projective plane

Let a projective plane of order q≥2 have v=q²+q+1 points and lines. Write M for its point–line nonincidence matrix. In any cover of its support by k valid rectangles, write S for their sum, with multiplicities counted. Put T=sum(S−M), the surplus above area q²v. If k≤v then

    T ≥ 2q²(v−k)/(sqrt(q³−q+1)−1).

The inequality is strict when v−k≥2. The plane requires no specified coordinatization.

M has all row and column sums q², and distinct rows have q²−q common ones. Consequently MMᵀ=qI+(q²−q)J and M⁻¹=Mᵀ/q−(q−1)J/q². Its entries at transposed allowed positions equal 1/q². Its columns have squared norm (q³−q+1)/q⁴, and distinct columns have inner product −(q−1)/q⁴, by inverting MMᵀ. Set E=S−M≥0, B=M⁻¹E and h=nullity(I+B). Since S is a sum of k rank-one matrices, h≥v−k. If P projects orthogonally onto this kernel, BP=−P. The reflection Q=I−2P gives tr(QB)=T/q²+2h. Nonnegativity and the coordinate bound on each QM⁻¹ column give tr(QB)≤T sqrt(q³−q+1)/q². Rearranging proves the assertion.

For strictness, rank E≥v−k since rank M=v. Rank at least two forces two positive entries in distinct rows and columns. At equality, every positive E entry would attain the componentwise norm bound. The two respective QM⁻¹ columns would then point along distinct coordinate axes and have zero inner product, contradicting their nonzero inner product before orthogonal reflection.

For q=5 and k=17 this gives integer T≥71 and total area ≥846. Additional integer shape accounting raises the area floor to 847. The projective-plane bound is a surplus-area constraint on rectangle covers.
