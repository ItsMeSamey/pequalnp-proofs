# Structural checks for L-meta-10007

The target is an all-zero rectangle cover of the supplied 31-by-31 binary matrix using at most 17 rectangles. Let Z denote its zero-position indicator (so a rectangle lies in the support of Z). The checks below give necessary conditions and method limitations, not a 17-cover or an exclusion of one.

## Exact closure and fractional cover

All rows and all columns of the supplied one-position incidence relation have size six; any two distinct rows or columns intersect in exactly one. The rows are simultaneous cyclic translates of row zero; its support is {4,6,7,20,26,30}. If a nonincidence rectangle has a points and b lines, count incidences from those a points on the 31−b available lines. The intersection sizes have sum 6a and sum of squares a(a+5). Cauchy's inequality gives (a+5)(b+5)≤180, so its smaller shore has size at most eight. Enlarge any rectangle to a maximal one without losing covered cells. To enumerate maximal rectangles, list candidate smaller shores containing index zero, take all allowable opposite-shore vertices, close back, and require equality. Enumerate both orientations, using only one when sizes coincide. Every nonempty proper shore has a free orbit of size 31 under the cyclic shift; choose one representative among its translates containing zero and restore the factor 31.

spectrum.cpp implements this census. spectrum.txt records all shapes and counts. The maximum area is 60; 3,100 rectangles each have shape (6,10) and (10,6). Every nonincidence cell belongs to exactly 480 of those rectangles, verified from the cyclic difference classes. Assigning weight 1/480 to each gives a fractional cover of size 155/12. Uniform dual cell weights 1/60 match that objective. Thus positive weights on cells alone cannot certify 14 by an unrounded fractional bound.

For an integer cover, assign each of the 25 cells of a row p to one covering rectangle. If a chosen rectangle has a rows and receives j columns at p, charge 1/a to this row; total charged across all rows is at most the number of chosen rectangles. The census bounds a by A_j=max{a: there exists a maximal rectangle (a,b) with b≥j}. The minimum of Σ1/A_j over integer partitions of 25 is 14/33, attained arithmetically by (10,10,5); a realizable geometrical assignment is not required for this lower bound. Thus at least ceil(31·14/33)=14 rectangles are necessary.

## Real-rank overlap obstruction

Suppose k rectangles cover all 775 nonincident cells. Let W be their ordinary integer multiplicity matrix (a sum of k real rank-one indicators), A=ΣW, and C_j,R_p the column and row sums of W. W vanishes on the forbidden positions. The given design has ZZᵀ=5I+20J and Z⁻¹=Zᵀ/5−4J/25. Hence tr(Z⁻¹W)=A/25, and

    ||Z⁻¹W||_F² = (1/5) Σ W² − (4/625) Σ C_j².

The absolute trace of any real rank-at-most-k matrix is at most sqrt(k) times its Frobenius norm, by singular-value Cauchy–Schwarz. This gives

    A² ≤ k (125 Σ W² − 4 Σ C_j²),

and likewise using the row sums. In particular (1/k+4/31)A² ≤ 125 Σ W². This derivation does not require Z⁻¹W to be symmetric.

If every covered cell has multiplicity at most two, Σ W²=3A−1550 and ΣW²/A²≤9/(8·775) by completing the square. Thus k≥248/13, or k≥20 integrally. For the general case let T=Σ binom(W−1,2) over the 775 covered cells. Then ΣW²=775+3(A−775)+2T. Minimizing the resulting lower bound in the integer range 775≤A≤60k proves T≥27 at k=17 and T≥14 at k=18. T counts excess pairs after discarding one hit per cell; it need not count distinct cells. Other values are reproduced by rank.py. A 14-cover with maximum multiplicity four is likewise impossible: W²≤5W−4 on the positive support and the same scalar inequality fails for 775≤A≤840.

A local refinement follows by applying the trace bound to diag(d)WZ⁻¹ and optimizing the row scale factors d independently. The diagonal entries before scaling are R_p/25 and the squared row norms are Σ_L W_pL²/5−4R_p²/625. Choosing d proportional to the ratio gives

    k ≥ Σ_p R_p² / (125 Σ_L W_pL² − 4 R_p²).

The transpose gives the column version. For a row with 25 multiplicities in {1,2}, the same squared ratio estimate gives a contribution of at least 8/13. Thus a 17-cover has at least four different rows and four different columns containing a triply covered cell. The inequalities can be used as pruning conditions only with attainable bounds for all unfinished rectangles. They do not preclude k=17.

## Code and fooling-set conditions

Give a point p the code C(p) of rectangles containing it. A line L rules out the coordinates U(L)=⋃_{p∈L} C(p). Coverage is exactly C(q) not contained in U(L) for q outside L if every rectangle is closed on its line side. The point codes are pairwise incomparable. For a partition C(p)=A ⊔ B, set F_A=(intersection of the point shores indexed by A) minus {p}, and similarly F_B. If both are nonempty they are disjoint by incomparability, and all points of F_A∪F_B lie on a single line through p: otherwise two witnesses q,r on differing directions provide a line qr missing p and meeting every owner of p. This includes the load-three and load-four restrictions on pair intersections.

A k-cell fooling set uses distinct row and column indices. Its k-by-k submatrix has at least k(k−1)/2 forbidden incidences, since each pair needs a cross incompatibility. If the row degrees there are d_i, the absence of four-cycles gives Σ binom(d_i,2)≤binom(k,2); convexity bounds k≤7. Equality at seven forces all seven row degrees equal three, equality of the pair bound, and hence a Fano subplane (a 2-(7,3,1) design). In a Fano plane a four-point quadrangle has collinear diagonal points; this follows, for example, by writing the four points as a,b,c,a+b+c over GF(2). The explicit matrix has 15,500 quadrangles and none has collinear diagonals, as checked directly by analyze.py. Six mutually incompatible zero entries are (0,0),(1,1),(2,4),(5,27),(25,9),(28,20). Thus the fooling-set bound is exactly six.

## Reproduction

Run analyze.py and rank.py with Python 3. Compile spectrum.cpp with a C++17 compiler, then feed its standard input the 31 decimal masks separated by spaces. Inputs are the exact public statement masks also recorded in ../official10007comb/rows.json (JSON brackets and commas must be converted to whitespace). No optimizer or external solver is used for this census.
