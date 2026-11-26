# A rational three-colour pair SDP certificate at degree six and girth six

Let G be a finite simple six-regular graph of girth at least six. For each vertex v form a row R_v with value 6 at v, −3 on its six neighbours, 1 on vertices at distance two, and zero elsewhere. There are 30 distinct distance-two vertices, since two distinct length-two paths from v to the same vertex would give a four-cycle. Thus ||R_v||²=36+54+30=120. Equivalently R=A²−3A for the adjacency matrix A.

For an edge vw the endpoints give two products 6(−3); the other five neighbors of each endpoint give ten products (−3)·1. There are no common neighbors and no vertex at distance two from both ends: its two shortest paths would make a triangle or a cycle of length at most five with vw. Hence R_v·R_w=−66. If v,w are distinct nonneighbors, negative products can only occur between a neighbor of one and a distance-two vertex of the other. Each orientation has at most six such products, so R_v·R_w≥−36; positive products can only raise the result.

Consequently T=(RRᵀ+12I)/132 is positive definite, has unit diagonal and equals −1/2 on edges. It gives a strict vector 3-colouring. Distinct nonneighbors satisfy T_vw≥−3/11, and all entries have absolute value at most one by Cauchy–Schwarz.

For the colour-pair relaxation, choose unit t_v realizing T, three unit simplex vectors s_c with inner products −1/2 across colours, and a fresh unit root e. Use vectors w_vc=e/3+(√2/3)(t_v tensor s_c), with the tensor space orthogonal to e. Each vertex sums to e, and each root-colour inner product and colour-vector squared norm is 1/3. With D_cd=2 for equal colours and −1 otherwise, their Gram entries are

    M_(v,c),(w,d) = (1+D_cd T_vw)/9.

They are nonnegative because all T_vw lie in [−1/2,1]. Each 3-by-3 block has row and column sums 1/3 and total one. At a single vertex the block is diagonal with entries 1/3; on an edge it has zero diagonal and off-diagonal entries 1/6. The augmented matrix on the root and all colours is positive semidefinite by its construction. These are consistent pair marginals and a PSD moment matrix; they do not assert existence of simultaneous colourings or feasibility of higher-order relaxations.

One can certify PSD using only integer features and a shared rational Gram denominator. Set B=[R | 2I | 2I | 2I], a=(8,8,2) and h_c=e_c−e_(c+1 mod 3). Assign integer feature (3a,0) to the root and (a,B_v tensor h_c) to each coloured vertex. Their integer Gram matrix divided by 1188 is exactly the augmented matrix above. In particular no numerical eigensolver is required.

The checker constructs the Levi graph of PG(2,5) using normalized projective triples and point–line orthogonality modulo five. It verifies 62 vertices, 186 edges, girth six, the integer factor, and all 34,596 ordered coloured pair entries. The nonedge T numerators over 132 are 50 and −36, so the lower estimate is attained. The fixture is bipartite and checks the boundary girth and arithmetic; it is not a non-three-colourability witness.

General SDP upper bounds for regular graphs of prescribed girth via local nonbacktracking polynomials were established by Banks, Kleinberg and Moore. Related vector-colouring bounds for irregular graphs were obtained by Banks and Trevisan. The calculation here gives a short radius-two certificate and verifies entrywise nonnegativity for the stated pair relaxation. No general priority claim is made. [Banks, Kleinberg and Moore](https://doi.org/10.1137/18M1180396) · [Banks and Trevisan](https://arxiv.org/abs/1907.02539)
