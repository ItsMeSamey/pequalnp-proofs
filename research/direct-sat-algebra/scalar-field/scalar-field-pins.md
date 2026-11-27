# Affine restrictions of scalar quadratic forms over a hidden field

Take a recovered or supplied full field chart for a centered homogeneous quadratic Q:K^d→K with nondegenerate polar B over K=GF(2^m), and translate any existing origin shift into target and affine constraints. Let h independent consistent binary constraints be given. The absolute-trace pairing Tr(B(.,.)) is a nondegenerate binary bilinear form, so write them as Tr(B(w_j,x))=c_j using elementary linear algebra. Set q=2^m, n=md, χ(s)=(−1)^Tr(s). Let G be the binary Gauss sum of Tr(Q). Every phase λQ with λ≠0 has the same total G because every nonzero λ is a square in K.

Expand the target and check indicators by orthogonality. At λ=0, only the trivial binary constraint character contributes since the rows are independent. For λ≠0 translate by w/λ in the input, with w=sum_j s_j w_j:

    sum_x χ(λQ(x)+B(w,x)) = χ(Q(w)/λ) G.

Thus the exact restricted target count is

    [ 2^n + G sum_s (−1)^(s·c) sum_{λ≠0} χ(tλ+Q(w_s)/λ) ] / (q·2^h).

The inner sum is q−1 if both coefficients vanish, −1 if just one vanishes, and an elliptic Kloosterman sum otherwise. The point-counting reduction of punctured-field-target.md makes the total 2^h times a polynomial in the explicit binary input dimensions. This applies to every nondegenerate scalar quadratic form in even dimension, including nonsplit binary norm forms. For N(z) from the quadratic extension, the nontrivial additive phase over N(z)=t≠0 may also be derived directly: write D=N(a)t, count elements w=az by trace s. There is one for s=0 and two for s≠0 exactly when X²+sX+D is irreducible, i.e. Tr(D/s²)=1. Summing the signs χ(s) gives −K(sqrt D), consistent with the nonsplit Gauss sign.

There is a deterministic polynomial witness for every target if d>2h. The K-orthogonal complement W of the K-span of the w_j has dimension at least d−h and radical dimension at most h. It contains a nonsingular two-dimensional plane P. Find such a plane by Gaussian elimination and any pair on which B is nonzero. Select an arbitrary basepoint x₀ satisfying the binary checks. Adding p∈P preserves all checks. Since B|P is nonsingular, a translation p₀∈P removes the linear part B(x₀,p) of the restricted quadratic. The resulting homogeneous form on P attains a nonzero value (its polar is nonzero) and attains zero at the origin. Scaling by field square roots therefore realizes any translated target on the same plane. All steps are polynomial and supply a direct input witness. This argument also applies whenever W has nonzero polar, independent of the sufficient numerical bound.

The original field chart must still be supplied or recovered from an unpinned description. These results alone do not recognize arbitrary restrictions of an unknown high-dimensional field form from their coefficients.
