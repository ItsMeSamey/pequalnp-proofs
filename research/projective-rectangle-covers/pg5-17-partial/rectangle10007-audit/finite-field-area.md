# Every 17-cover has total area at least 850

This is a necessary condition and does not resolve the existence of a 17-cover. It applies to the ordinary multiplicity matrix W of the chosen rectangles, before or after maximalization. Start with the independently audited area lower bound 847. Write E=W−Z, a nonnegative integer matrix supported only on the zero-entry indicator Z. The scalar excess t is the sum of E. A row type is the partition of its row excess into its positive entries. Allow any such partition; there is no partial-permutation hypothesis in the following tests.

## Real filter

For a row type q put e=sum(q), Q=25+2e+sum(v² for v in q). The row contributes at least f(q)=(25+e)²/[125Q−4(25+e)²] to the trace rank inequality of README.md. The sum of these f(q) must be at most 17. The exact secant from the five-anchor audit, s=17125/93899 and b=3030/93899, gives g(q)=f(q)−1+se+b≥0. For 31 row types of total excess t the total gap is at most ts+31b−14. Consequently any individual type with gap above that budget can be rejected. For a given positive e the pure type (e) minimizes the gap since it maximizes Q. Only types (2) and (3) have zero gap.

## Two finite-field filters for splits

Over F_p, p=2 or 3, Z is invertible: ZZᵀ=5I+20J with eigenvalue 625 on the all-ones direction and 5 on its complement over the reals, so its determinant is 625·5³⁰. Let R be the rows of E with any entry nonzero mod p, and r=|R|. The matrix WZ⁻¹=I+EZ⁻¹ has nullity at least fourteen. A kernel vector must vanish outside R because those rows are the corresponding identity rows. The restriction B=(I+EZ⁻¹)[R,R] therefore has the same nullity, so r≥14 and rank B≤r−14.

For p=2 call a row pure here if just one defect entry is odd; even defects in other columns are permitted. Z⁻¹=Zᵀ mod2. The B row of a pure row i with odd defect at line l is e_i plus the values Z(p_j,l) for active point rows j. Its diagonal is zero. Four equal pure rows would therefore vanish on all four respective columns. Their odd defect lines must be distinct, since two rows with the same line differ in their e_i term. Each of the four lines then contains the three other points from the group. This forces two distinct lines to share at least two points. Thus the number of pure rows is at most 3·2^(r−14), even when the other rows split.

For p=3 call a row distinguished if its list of nonzero residues has just one entry, equal to 2. Write m for the number of these rows. The entries of Z⁻¹ are 1/25 or −4/25, reducing to 1 or 2, respectively, with 1 on the support of Zᵀ. The diagonal of each distinguished B row is 1+2=0 over F₃, while all its off-diagonals are nonzero. In particular these m row vectors are nonzero if r≥14, and no two are proportional because their zeros are in different positions. Hence m≤(3^(r−14)−1)/2.

A stronger quadratic inequality is available. Restrict B to the principal m-by-m submatrix on the distinguished rows and square each entry over F₃. The result is J−I, of rank m minus one if m≡1 mod3, and rank m otherwise. On the other hand the entrywise square of a rank-d matrix has rank at most d(d+1)/2: square an expansion of its entries as dot products of d coordinates and use the symmetric degree-two monomials. Therefore

    m − 1_{m≡1 mod3} ≤ (r−14)(r−13)/2.

## Finite enumeration

Run python higher_excess.py 72, 73, and 74. The program enumerates all allowed row types and their multisets exactly using fractions. It determines counts of (2) and (3) from the number of remaining rows and remaining total excess; those two integer equations have a unique solution. Type order is immaterial. The following counts remain after each necessary test:

| total excess | real | mod2 | mod3 nonzero rows | mod3 projective row bound | mod3 entrywise square |
|---:|---:|---:|---:|---:|---:|
| 72 | 13 | 1 | 0 | 0 | 0 |
| 73 | 133 | 39 | 7 | 0 | 0 |
| 74 | 935 | 318 | 68 | 16 | 0 |

Thus no area 847, 848, or 849 is possible. Area 850 is not ruled out: at t=75, the same necessary tests leave 37 row histograms. The finite-field cuts use row types only, allowing both split rows and repeated column supports.
