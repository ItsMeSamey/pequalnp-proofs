# Exact port tables from linked exterior components

Use the auxiliary graph, labeled edge pivots and fixed physical pin pairs (1,0) of the [three-to-three linking construction](rooted-full-boundary-linking.md). No inner table is needed to analyze this exterior. If the link does not exist, the construction gives an actual separating cut of rank at most two. Otherwise denote the six virtual port bits by w, their quadratic form by q(s,t)=s·t, and its alternating polar by J. The algorithm below computes every attainable w and lifts one real exterior selection for each. Any such state can be joined to a verified inner representative. An incomplete inner table alone cannot certify NO merely because none of its entries match.

On each deleted real site use as z_i the original input or output that was clamped to zero in its deletion chart. Endpoint swaps specify which. The pin equations and these clamps form a nonsingular square linear system on the inputs of the auxiliary graph. With homogeneous right-hand sides the final six-vertex graph has zero pin symbols; its cross block is invertible, so the final word is zero. Reversing deletion and pivot then gives only zero. Holding the original pins fixed, Gaussian elimination with arbitrary clamp right-hand sides now supplies the other real coordinates a+Hz, the port bits w=w₀+Cz and the original input word as an affine function of z. The sites are legal exactly when z_i(a+Hz)_i=0. The graph is simple, and swapping coordinates preserves the product at each site, so the polynomial identity on all Boolean z is

    zᵀ(a+Hz) = q(w₀+Cz).

In particular q(w₀)=0, H+Hᵀ=CᵀJC and a_i+H_ii=q(C_i)+C_iᵀJw₀, where C_i is column i.

Process strongly connected components of the row dependency graph of H so earlier rows are independent of later columns. At a component B retain the six-bit syndrome σ of the already chosen real coordinates. The past contribution to its equations is C_BᵀJσ. Try each local increment d in im C_B. If a legal u exists with C_Bu=d and with selected coordinates satisfying (a_B+H[B]u+C_BᵀJσ)_i=0, retain its witness and update σ to σ+d. One predecessor per state suffices. At the end evaluate the original affine reconstruction. This also handles choices for which a different set of clamps gives a singular boundary system. The [native enumeration implementation](exterior_chart_dp.py) takes polynomial time times 2 to the largest component size. There are at most 64 syndromes throughout.

## Eliminate every component of port rank at most two in polynomial time

Write C_B=L V with L a six-by-k basis matrix and V of row rank k, including k=0. Let d=L e. Choose a k-by-k binary matrix R with xᵀRx=q(Lx) for every x, by placing the squarefree mixed coefficients above its diagonal. Then R+Rᵀ=LᵀJL. Put H'=H[B]+VᵀRV, which is symmetric, and clear its diagonal to make a simple graph A. Under Vu=e the same local zero-product equations now ask for selected degree in A equal to (Vᵀλ)_i, with

    λ=LᵀJ(w₀+σ)+Re.

Indeed the diagonal correction is diag(H[B])+q(C_i) at site i, canceling both terms in the coefficient identity above. Handshaking on A requires e·λ=0. If this holds choose a symmetric k-by-k T with Te+diag T=λ. For e=0 use the diagonal. Otherwise conjugation of coordinates is unnecessary: use diagonal entries to match λ outside the support of e, and add off-diagonal disjoint pairs matching ones of λ on its support, whose number is even. Clear the diagonal of VᵀTV and add it to A. For a selection of label sum e the new contribution at each selected i is V_iᵀ(Te+diag T)=V_iᵀλ. We have obtained exactly an all-even induced selection with prescribed k-bit color sum e, with the identical local selection as witness both ways.

For k≤2 the [two-readout support-or-cut algorithm](two-readout-even-p3.md) solves this in polynomial time. A zero target uses the empty set; one row can be embedded in the binary plane. Larger k can use direct local enumeration. Thus the complete exterior table is computable in polynomial space and in time polynomial in the graph size times 2^b, where b is the largest size of a component of port rank at least three (b=0 if none). This improves the largest-SCC bound, for example on arbitrarily large connected symmetric real blocks of one port color. More generally any certified all-even k-readout procedure can be used on the displayed component and target. This local bound does not invoke an unrestricted three-readout decision procedure.

## The hard-component size is intrinsic to linked clamp choices

The [projection proof](linked-chart-scc-invariance.md) shows that all directional cut ranks and the SCC partition are invariant under changing the linked orientation while the named physical relation is fixed. The port rank of each component is also invariant. For a change of the chosen coordinates on K the new free coordinate map retains z outside K and replaces z_K by the corresponding old alternates. It is invertible precisely when H[K] is invertible. In SCC order it is block triangular, hence the changes can be made one component at a time. Previously changed earlier blocks cannot change the diagonal block of any later component, since the earlier rows are independent of later variables.

Consider a change on K within component D. For B=D, the columns of C on D change by right multiplication by an invertible matrix (hold every outside coordinate fixed). For D earlier than B they do not change. For D later than B, the new columns on B are

    C'_B=(I+C_K H[K]⁻¹ C_KᵀJ) C_B.

Here H[K,B]=C_KᵀJC_B by the one-directional dependence. The determinant lemma and C_KᵀJC_K=H[K]+H[K]ᵀ give determinant det(H[K]ᵀ)/det(H[K])=1 for the left multiplier. All three cases preserve the rank. The port bits in this statement are the original port bits; a fixed invertible reordering of them also preserves rank.

Physical full-rank-six families with all singleton components or one component as large as desired are supplied in the [companion constructions](linked-chart-scc-invariance.md). Consequently changing the linking sequence cannot guarantee that only small high-port-rank components remain. The private rank-two replacement, all-even two-readout solver, and claims here address the physical pin problem. No unrestricted CircuitSAT complexity consequence is derived.
