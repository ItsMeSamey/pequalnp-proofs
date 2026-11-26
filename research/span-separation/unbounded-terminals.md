# Binary terminal span and avoidance

Given ordinary binary columns A, vectors u,w, and a supplied subspace K containing u, seek X such that u belongs to span(A_X) and w does not belong to K+span(A_X). Equivalently seek a covector φ with φ(K)=0, φ(w)=1, and u in the span of the ordinary columns it annihilates. This is finite-dimensional linear separation. Witness subsets can be verified in polynomial time by Gaussian elimination.

## NP-completeness with four ordinary columns per block

Reduce graph 3-colorability. For a nonempty simple graph introduce global coordinate vectors Z_v,T_v for each vertex v and another global coordinate w. The separator's values on Z_v,T_v will encode colors 00,01,10. Introduce one block for each vertex and edge. A block has two expressions L_1,L_2:
* For vertex v use Z_v,T_v.
* For edge ij use Z_i+Z_j+w,T_i+T_j+w.

The intended test for a block is φ(L_1)=0 or φ(L_2)=0. Since φ(w)=1, the vertex tests exclude 11 and the edge tests require different binary pairs.

For each block b independently introduce three local coordinate vectors u_b,a_b1,a_b2 and put exactly four columns into A:

    a_b1, a_b1+u_b, a_b2, a_b2+u_b.

Set u=sum_b u_b. Let K be spanned by u and the vectors a_bj+L_j for each block and each j. This is an independent listed basis: the vectors other than u have private a_bj pivots, and u is nonzero on local u_b coordinates. Apart from u each listed K vector has weight at most four. Also w does not belong to K by the same private-coordinate test. The ordinary vector matroid is a direct sum of four-element circuits; every block has rank three and any proper subset is independent. Thus it is both graphic and cographic. No regularity claim concerns the jointly augmented representation.

For the forward implication take a feasible subset and a separating φ. All ordinary columns lie in independent local block spaces. Since the selected columns span u, within every block its selected zero columns span u_b. Hence φ(u_b)=0 separately for every b, and both columns in each pair have the same value φ(a_bj)=φ(L_j). If both expressions were nonzero then no zero column would be available in that block. Thus every block test passes. The global coordinates now give a proper three-coloring.

Conversely, assign φ(Z_v),φ(T_v) the bits of a proper coloring. Set φ(w)=1, each φ(u_b)=0 and each φ(a_bj)=φ(L_j). These prescriptions define a linear functional on the coordinate basis and annihilate all of K, including u. Every block has a true test and its corresponding pair is annihilated. Choose one such pair per block. Its two columns sum to u_b, so altogether the chosen columns span u. The separator certifies avoidance of w. This polynomial-time reduction and verification establish NP-completeness for unbounded supplied K containing u.

## Deterministic nonregular subclasses

Suppose A is partitioned into supplied independent vector-space summands with nonzero local targets u_b whose sum is u. In each summand assume the ordinary columns occur in pairs a,a+u_b. Pair representatives can have arbitrary dependencies. Solve φ(K)=0, φ(w)=1 and φ(u_b)=0 for all b, obtaining an affine space D. If inconsistent, reject. Within D each block fails on the affine flat F_b specified by φ(a)=1 for every pair representative. Exactness follows from the paired columns and independence of the summands as above.

When every nonempty failure flat has codimension at most one in D, its avoidance gives another linear system: a full-space failure rules out any solution and the complement of a hyperplane gives the opposite affine equation. This exact polynomial algorithm permits unrestricted K and local nonregular ordinary matroids, such as saturated configurations containing the Fano plane as a restriction. More generally, if the sum of the relative sizes |F_b|/|D| is less than one, a deterministic polynomial algorithm finds a witness. Fix the free coordinates of D successively, choosing at each step a value for which the sum of conditional relative sizes does not increase. Gaussian elimination computes the sizes, and averaging guarantees such a value. At a full assignment this sum must be zero. If instead all block predicates reduce to constants or literals of free coordinates and each block has at most two pairs, ordinary 2-SAT solves the instance exactly.

## Arbitrary binary columns when K=span(u)

Because a witness must span u, adding u to K leaves feasibility unchanged. Thus the case K=span(u) is equivalent to K=0. The following deterministic polynomial algorithm applies without any ordinary regularity assumption.

Reject if u lies outside the ordinary span or w=0. When w lies outside the ordinary span, any ordinary representation of u works. Choose the empty witness if u=0 and w≠0. Reject u=w. In the remaining case u,w are independent members of the ordinary span. If a witness exists, choose an independent subset spanning u. It projects injectively modulo w. Extend its image by ordinary columns to a basis modulo w. The corresponding lifts give a hyperplane containing u and excluding w, so testing all quotient bases would suffice.

Choose one ordinary basis B modulo w. Its lifts together with w form a basis upstairs. If those lifts span u return B. Otherwise write u=w+s with s in span(B). In coordinates relative to B and w the ordinary matrix has projections modulo w and modulo u given by V and V+s h^T, where h is the last-coordinate row of the original columns. Both matrices have B as identity. A witness exists precisely when a basis of V is singular after the update.

Build a bipartite graph with B rows and nonbasis columns, joined where V_ij=1. Breadth-first search from all rows with s_i=1 toward columns with h_j=1. A shortest path is induced, with no special interior vertices. Write it r_1,c_1,r_2,c_2,...,r_t,c_t. Its V submatrix is lower bidiagonal with diagonal ones, and the last coordinate of its inverse applied to the first unit vector is one. Exchanging these B rows for these columns yields a V basis. The corresponding updated submatrix differs only by the outer product of the first and last unit vectors; its determinant multiplier is 1+(V_sub^{-1})_{t,1}=0. Hence the exchanged basis solves the instance.

If there is no path, each graph component lacks either an s-support row or an h-support column. For any V basis exchanging I rows for J columns, V[I,J] is nonsingular. By graph components it is block diagonal with square nonsingular blocks, since any nonsquare component block would prevent invertibility. Therefore h_J^T V[I,J]^{-1}s_I=0, and the updated minor stays nonsingular. There is no witness. The algorithm uses Gaussian elimination and one breadth-first search.

Run exchange.py to compare the witness algorithm against direct subset enumeration on 9,392 instances, including all simple rank-at-most-three binary configurations and all terminals in the chosen three-dimensional ambient space. Run check_terminals.py to compare the 3-color construction against general binary separator enumeration on all 75 labeled simple graphs of orders one through four.
