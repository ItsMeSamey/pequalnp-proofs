# Counting one-direction principal-support differences on a common rank decomposition

Let J and K be symmetric n by n matrices over a fixed finite field F of order Q, on the same labeled indices. On a supplied rooted binary tree with those leaves, let k be the maximum of the two off-diagonal cut ranks over its edges. A deterministic algorithm counts masks S in each of the four classes given by the singularity of J[S] and K[S]. It can recover a mask in any nonempty class. It uses Q^{O(k²)} poly(n) bit time and space. Singularities here are ordinary linear dependencies even in characteristic two. The empty matrix is invertible. The count distinguishes gains from losses, including for the quaternary rank-one update. A different calculation on the same tree counts actual binary solutions to the center equations with r linear readouts in 2^{O(k+r)} poly(n) time and space.

## Principal masks

Treat each matrix M separately when computing boundary coordinates. For node I, choose a full column basis U_I of the column space of M[I,complement I], of width k_I. At the root take zero columns. The state for a mask S contained in I records a linear relation on F^{k_I} × F^{k_I}

R_S = {(h,p) : there is an x in F^S with M[S]x + U_I[S,:]h = 0 and p=U_I[S,:]^T x}.

It also records whether the space of such x at h=p=0 has positive dimension. Denote that dimension by z_S before saturation to one bit. Every attainable (h,p) has exactly Q^{z_S} realizations by linearity. The field transpose here has no conjugation. At a leaf compute both mask choices by linear algebra, including an omitted leaf with unrestricted h, p=0, and z_S=0.

For children L,R of I there are computable matrices D,T_L,T_R with

M[L,R]=U_L D U_R^T,   U_I[L,:]=U_L T_L,   U_I[R,:]=U_R T_R.

The cut-column spaces and, by symmetry, the cut-row spaces give these factorizations. Full column rank gives left inverses and a method to compute them. Fix child relations R_L,R_R. For trial h,p,p_L,p_R impose

(h_L,p_L) in R_L,   h_L=T_L h+D p_R,
(h_R,p_R) in R_R,   h_R=T_R h+D^T p_L,
p=T_L^T p_L + T_R^T p_R.

Projection to (h,p) is the parent relation by direct substitution into the block equations. Let delta be the dimension of the solution space in (p_L,p_R) with h=p=0. For each such pair the internal variables in the children independently have Q^{z_L} and Q^{z_R} realizations. Each assembled pair of internal vectors gives unique (p_L,p_R). Thus z_S=z_L+z_R+delta. For the recorded bit this requires only the child bits and testing delta>0. These facts cover singular child blocks that become nonsingular after a join, and interior kernels that cannot couple across the cut.

Store the pair of canonical relation bases and bits, one for J and one for K. The common leaf choice is indispensable. Merge by adding the product of child selection counts to the parent state. Distinct choices correspond bijectively to the child mask pair, irrespective of how many kernel vectors exist. Keep a child-pair pointer for reconstruction. At the root the two bits give the true singularities. For each relation on dimension at most 2k there are at most Q^{O(k²)} distinct reduced bases; pairs and their Cartesian products have the same asymptotic bound. All table counts have at most n+1 bits. Root mask verification uses the two original determinants. In the [two-readout application](two-readout-principal-sieve.md), a gain supplies a binary kernel vector with a·x=1, b·x=0 by solving the original principal equations over GF(2) and restricting to its actual support. Counts of gained principal masks and counts of binary witnesses are different quantities.

## Obtaining a bounded-width tree

For a matrix M, form the arrangement of subspaces W_i=span(e_i,M[:,i]) in F^n. The sum on side I has dimension |I|+rank M[complement I,I], by eliminating the I coordinates using the e_i. The sum on the full ground set has dimension n. The dimension of the intersection of the two side sums is therefore twice the cut rank for symmetric M. For a pair use W_i(J) direct sum W_i(K) on disjoint ambient copies of F^n. The connectivity on each cut is twice the sum of the two cut ranks. The finite-field subspace arrangement branch-decomposition algorithm of Jeong, Kim and Oum constructs a tree of width at most w if one exists, or certifies the bound fails. Thus a tree having both individual ranks at most k guarantees success with w=4k, and the returned individual ranks are at most 2k. The cost of this search is their fixed-parameter construction time, additional to the explicit evaluation time for a supplied tree. A degree-two root can subdivide an edge. Small ground sets can be evaluated directly. [Jeong, Kim and Oum](https://arxiv.org/abs/1711.01381)

The use of graph decompositions for principal ranks has precedents. Courcelle evaluates bounded portions of a multivariate interlace polynomial at bounded clique-width. Bläser and Hoffmann develop Gaussian elimination states at bounded treewidth for a single binary graph polynomial. The relation above gives an explicit shared-mask computation over a fixed finite field for two supplied symmetric matrices. [Courcelle](https://arxiv.org/abs/cs/0702016) [Bläser and Hoffmann](https://arxiv.org/abs/0902.1693)

## Direct binary witness counts

For native binary H with readout matrix T of row rank r, the target is x_i(Hx)_i=0 on all indices together with Tx=d. Use the cut bases of H. For node I store, indexed by h,p in GF(2)^{k_I} and s in GF(2)^r, the number of x_I satisfying

x_i ((H[I,I]x_I)_i+(U_I h)_i)=0 for each i in I,
p=U_I^T x_I,   s=T[:,I]x_I.

Leaves try both input bits at each h. At a join enumerate h,p_L,p_R,s_L,s_R. Form h_L,h_R,p by the displayed join equations and add the product of the two child counts to entry (h,p,s_L+s_R). Fixing h at the parent, each x_I has unique child emissions, hence contributes exactly once. The root entry at h=p=0,s=d counts all original center assignments. A stored positive pair yields one such assignment. Raw private leaves are restored individually by their original equations in the native P3 application. This counts centers, including singular cases, and does not count every leaf completion. The time bound follows by enumerating at most 2^{3k+2r} tuples per node, and every stored count for fixed h fits in n+1 bits. For the quaternary update the two cut ranks are bounded by rank(H_cut)+2 since each added outer product has rank at most one.

For the even path, every invertible-diagonal completion scheme has correction rank at least n/2 by its triangular odd/even submatrix. A prefix tree in path order has cut rank at most one for H, so both algorithms above are polynomial for the quaternary update and two readouts. At the opposite extreme, in any bounded-degree family of graphs with constant edge expansion every binary cut tree has an edge with both sides of size at least n/3 (for n≥2). Its crossing graph has linearly many edges. A greedy induced matching in that bipartite crossing graph retains linearly many, since selecting one edge excludes at most O(Delta²) crossing edges for maximum degree Delta. On the selected endpoints the crossing adjacency submatrix is an identity up to ordering, forcing linear cut rank. This last implication is conditional only on the stated graph properties, independent of the diagonal and readouts. Thus these width-based time bounds by themselves give no polynomial bound on general principal-support inclusion or CircuitSAT.
