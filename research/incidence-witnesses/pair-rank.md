# Exact determinant of the local incidence matrix

Let a projective plane of order q≥2 have N=q²+q+1 points and lines. Write m=binom(N,2). Form an m×m zero-one matrix M with rows the unordered pairs of points and columns the unordered pairs of lines. An entry is one precisely when the incidences between the two pairs form an induced matching. Then

    |det M| = q^{m−N(q−1)}.

In particular M has full rank over every field of characteristic zero or prime to q. This includes characteristic two for odd q. The exponent is positive, so M is singular in every characteristic dividing q.

For the unique multilinear polynomial of any Boolean extension of the sparse incidence promise, the coefficient of x_p x_r y_l y_j for p≠r and l≠j equals −M[{p,r},{l,j}]. Indeed the coefficient is determined by evaluations below this four-bit input, all of which are promised. In inclusion–exclusion for the OR of its incident edge monomials, the contributing subgraphs must cover all four vertices. With two independent edges only their pair contributes, with sign −1. With three edges the unique matching and the full path cancel. An induced four-cycle is excluded, and all other configurations lack a covering edge subset.

## Proof of the determinant

Use real coordinates and Euclidean volume until taking the determinant. Let A be the point-line incidence matrix, so AAᵀ=qI+J by unique joins. For each point pair p,r write d for its join. Define the point-side flag embedding by sending a flag array g(d,p) to the pair array g(d,p)+g(d,r). Each block of q+1 points on a line has at least three points. All pair sums determine all flag entries, so the image has dimension N(q+1). Define the dual line-side embedding analogously.

The transpose of M sends the point flag image to the line flag image. For two columns l,j with c their intersection, induced matchings are in bijection with p∈l minus c and r∈j minus c. The contribution from g(pr,p) sums to

    h(c,l) = Σ_{p∈l, p≠c} Σ_{d∋p, d≠l} g(d,p).

The other flag contribution is h(c,j). The flag map therefore consists of two consecutive switches, first at each point, then at each line. Each local switch is J−I on q+1 entries, with eigenvalues q and −1. Both switches are invertible, and their combined absolute determinant in flag coordinates is q^{2N}. The Euclidean volume factors of the point-side and line-side flag embeddings are equal because each consists of N copies of the same pair-sum block. They cancel, leaving q^{2N} as the absolute determinant on the flag subspaces. By point-line duality M sends the line flag image to the point flag image, so Mᵀ maps orthogonal complements into orthogonal complements.

Identify a complementary point array with a symmetric zero-diagonal matrix F by writing F_pr=f({p,r}). Orthogonality is exactly Σ_{r∈d, r≠p} F_pr=0 for every flag (d,p). In particular F·1=0 by summing at p over its lines. Now AᵀFA is symmetric and zero-diagonal by the flag sums. For l≠j its off-diagonal entry sums F_pr over p∈l,r∈j. The terms using c=l∩j in either position sum to zero, again by the flag sums. The others give exactly (Mᵀf)({l,j}). Finally

    ||AᵀFA||²_F = tr(Fᵀ(qI+J)F(qI+J)) = q² ||F||²_F.

Passing between unordered pairs and symmetric matrices introduces the same factor on both sides. The complementary map is thus a scaled isometry, with volume factor q^{m−N(q+1)}. Multiplying the two orthogonal factors gives the determinant stated above. Since M has integer entries this also proves the rank assertion over finite fields.

## Consequences for circuit models

Even if validity is required only when each side has Hamming weight at most two, every representation as a sum of R products of arbitrary point-only and line-only functions needs R≥m over the stated fields. Multilinearize each factor on its own side and extract the quartic coefficients. Each product contributes an outer product, and their sum has rank m. A two-phase algebraic branching program with a layer separating all point-variable edges from all line-variable edges factors through its layer vertices and requires width at least m there. These conclusions concern this specified separation of variables.

On the full promise an exact value-matrix argument gives a larger two-phase bound without a characteristic restriction. Each nonempty line mask T with |T|≤q defines the column function OR over the point coordinates in its union U(T). If a line is outside T, at most q of its points belong to U(T). Thus T can be recovered from U(T). The functions OR over distinct nonempty point sets are linearly independent on the full Boolean point cube, as their multilinear coefficients are a signed inclusion matrix with unit diagonal after inclusion ordering. The exact rank on these columns is therefore Σ_{j=1}^q binom(N,j). The all-zero mask contributes a zero column.
