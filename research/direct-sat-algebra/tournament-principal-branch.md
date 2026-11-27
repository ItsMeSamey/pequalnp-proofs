# Neutral principal elimination with physical pins

Over F2 let M have complementary opposite off-diagonal entries. Feasibility requires x_i(Mx)_i=0, a specified affine readout Lx=t, and optionally named coordinates equal to one. Choose a neutral index set U with nonsingular A=M[U,U], and let V be its complement. This calculation handles the branch (Mx)_U=0. Set B=M[U,V], D=M[V,V], H=A inverse; use columns of ones of the appropriate lengths. Then x_U=HBx_V, and the branch is exactly the same support problem on

S=D+(B^T+11^T)HB,    L'=L_V+L_U HB.

Every retained named coordinate survives. All branch witnesses uniquely lift. Schur elimination uses polynomial bit operations over F2. The extra skew S+S^T+D+D^T equals B^T(H+H^T)B+1z^T+z1^T for z^T=1^T HB. It has rank at most rank(B)+2. For a lower bound take both shores of size m, A=D the upper triangular all-ones matrix, B=I. These blocks define a tournament with unit loops. H has ones on diagonal and first superdiagonal. Its symmetrization is the path adjacency of rank m for even m and m−1 for odd m (tridiagonal determinant recurrence or solve alternating-coordinate kernel). Subtracting a rank-two matrix changes rank by at most two. Thus the new skew defect can have rank at least m−3, also when up to three retained vertices are named. This concerns matrix representation on the single indicated branch; it is not an obstruction to deciding its scalar feasibility.

A singleton neutral vertex always splits into x_i=0 or (Mx)_i=0. If M_ii=1 the latter branch uses this Schur representation; the branches overlap, which is harmless for decision and precludes naive addition for counts. A whole chosen block need not be on the zero-readout branch in a witness.

## Compiling a transitive neutral shore for decision

Assume U has unit loops and transitive order with upper triangular all-ones principal matrix. Put k=rank B and write b_i=v_i^T R for its rows, with R a basis of the row space. For each increasing subsequence P allow x on it and impose (Mx)_P=0, forcing all other U bits zero. The union covers every witness by taking P to be its selected indices. For each i of P let j be its successor, with boundary row zero for the end. The lifted coordinate x_i=(b_i+b_j)x_V because the inverse is bidiagonal. The residual matrix and readout corrections are sums of the outer products

(1+b_i^T)(b_i+b_j),    l_i(b_i+b_j),

where l_i is column i of the h-row readout. Simultaneously accumulate these by summing compressed outer products [1;v_i;l_i](v_i+v_j)^T. Left multiplication of the first k+1 rows by [1,R^T] and right multiplication by R restore the matrix correction; the last h rows times R restore the readout correction.

Scan in transitive order, skipping freely or appending a new last term. Store the unfinalized (k+1+h)-by-k accumulator and the last (v,l), or a sentinel. Appending j finalizes the previous last contribution, and termination finalizes the last against zero. Equal states at the same layer are interchangeable. At most (1+2^(k+h))2^(k(k+1+h)) states suffice per layer with polynomial per-transition work. Store predecessors for witness recovery. The compiled disjunction has no new variables or readout rows, retains all named coordinates in V, and repeated residuals may be merged. Its skew perturbations obey the preceding rank bound for P using B_P. Membership of a physical assignment in several subsequences prevents directly summing residual counts. Low rank, choice of a sufficiently large transitive shore, and tractability of the resulting outside instances each require separate justification.
