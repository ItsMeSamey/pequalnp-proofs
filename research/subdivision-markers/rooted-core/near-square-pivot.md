# Bounded-type chain matrices in both orientations need not bound rank

Assume the near-square hypotheses of joint-forcing-rank.md, with exactly one exception of each kind in both orientations. Let A be the first support and B its complement. Both are circuits and cocircuits: a nonempty cycle with nullity one must be a circuit when its entire support is prescribed; dualize for cocircuits. The ordinary max-A basis comprises A except one element a₀, plus one element b₀ of B. With rows ordered by A in the basis followed by b₀, and columns by B outside the basis followed by a₀, its nonbasis matrix is

    [ N    1 ]
    [ 1ᵀ   0 ].

Indeed the two cycle and two cocycle identities force the displayed exceptional entries, even row and column sums of N, and odd row and column counts. In the reversed orientation the two exceptions also have size one, so rank N is one less than both dimensions (rank of B is 1+rank N). Thus N is n-by-n, n odd, of rank n−1, with both nullspaces spanned by the all-ones vector. Every one-row/one-column cofactor C obtained by deleting row i and column j is nonsingular, since the adjugate is the nonzero all-ones matrix.

Pivot on the row/column sets of C, retaining the old exception b₀ and the old A basis row i. In the resulting max-B basis, the clean block with rows (new B pivots,b₀) and columns (old A pivots,a₀) is

    border(C⁻¹) = [ C⁻¹      C⁻¹1     ]
                   [ 1ᵀC⁻¹    1ᵀC⁻¹1  ].

For an old A pivot column its new B-pivot coefficients solve Cx=e_j, and its old b₀ coordinate is recovered by summing x. For a₀ replace e_j by the all-ones column. This proves the entire clean block.

Let F be the m-by-m inclusive lower triangle and E=F+I its strict lower triangle. Form C with diagonal blocks F and off-diagonal blocks E. Then C=I+J₂⊗E, where J₂ is all ones, so C²=I in characteristic two. Every row and column sum of C is odd. Put N=border(C). This is a valid clean block of size 2m+1, even row and column sums, and rank 2m. The displayed full chart gives the required unlabelled circuit/cocircuit supports. The reverse reference chart obtained by pivoting C has exactly the same clean block N. Each of the four main blocks is a chain matrix (nested row neighborhoods), and rows within either main row type are globally nested across both column blocks; its border column is constant there. The same holds dually for columns.

All max-A charts and max-B charts still have bounded typewise chain complexity. Extend the reference clean block to D on A×B by a zero row and a zero column at the omitted/reference elements. For any new pair of reference elements a,b, its clean matrix has entries at i≠a,j≠b

    Dᵢⱼ + Dᵢb + Dₐⱼ + Dₐb.

Indeed j+b is a sum of A columns, and its coefficient vector has exactly two choices differing by the entire circuit A. Taking the representative with zero coefficient at a gives the formula. Every choice is a valid basis because B is the cocircuit complementary to the hyperplane spanned by A. The formula is row and column complementation followed by restriction. Refine each old row/column type by its associated complement bit; on every refined block the entries equal an old chain block or its complement, still a chain block. Use separate singleton types for the border and reference. At most eight row types and eight column types suffice uniformly. The identical reference reverse chart gives the argument in the opposite orientation. This asserts typewise nesting in arbitrary charts, not global nesting after arbitrary column complementation.

True marker uniqueness excludes this family for m>4−dim H. At index i take its two main rows and its two main columns across both copies. The internal two-by-two block is identity. Between different packets every two-by-two cross block is all zero or all one. Consequently the union of any subset of packets has odd degree at each selected row and column; the exceptional effects cancel within each packet. Each packet's fundamental-cycle/cocycle toggle has a gain g_i in the four-dimensional score space modulo H. The gain of any union is its sum. A nonempty zero-gain union would give a different support pair in the same q fiber. Thus all g_i are independent if q is unique, proving the stated uniqueness-only bound. With the additional missing score p, all packet subsets attain the entire coset q+span(g_i)+H, which must be proper in the four-bit space. Thus the joint hypotheses give the sharper m≤3−dim H. Dense all-one cross blocks preclude reasoning from induced matching size alone. The construction refutes an inference from bounded typewise chain behavior alone, not from the full marker hypotheses.

For a separate quick uniqueness test, take any clean N, set the selected columns to c and rows to Nc, and restrict c to ker(I+NᵀN). Every selected vertex has odd degree. Score gain modulo H and both exceptional effects are linear maps of c. Their combined map must be injective on the kernel for a unique q, giving nullity at most 4−dim H plus the two exception counts.

With a globally missing score the spectral bound also improves by one. On the subspace of that kernel annihilating all exceptional effects, every choice realizes the corresponding score coset. Its injective score image modulo H must have dimension at most 3−dim H, since otherwise all scores occur. Thus nullity(I+NᵀN) is at most rank of the exceptional-effect map on that kernel plus 3−dim H.
