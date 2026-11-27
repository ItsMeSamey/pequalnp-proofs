# A shared physical correction for all parallel queries

In PG(2,q), q=2^k, a binary monotone circuit of size 3kq²+O(q²) preserves every incidence flag and is exact for arbitrary payload whenever all active affine nonvertical queries have one slope. Vertical queries and the infinity query may simultaneously be active.

Let A_a = OR_b Y_ab and B_b = OR_a Y_ab for lines y=ax+b. Build R_jv as the OR of A_a over slopes whose j-th binary digit is v. Starting with D_0(x,y)=X_xy, update

D_{j+1}(x,y)=(R_j0 AND D_j(x,y)) OR (R_j1 AND D_j(x,y+e_j x))

for binary basis elements e_j of the field. This costs three gates per cell per digit. A single active slope a selects exactly one shift per digit, so D_k(x,b)=X_{x,b+ax}. OR these signals over x, intersect with B_b and OR over b. No ordinary query gives all-zero B. All ordinary flags survive multiple slopes by monotonicity. The ordinary query against its direction point uses A_a, each vertical query tests its column or vertical direction point, and the infinity query tests all direction points, with combined O(q²) extra gates.

For any nonempty ordinary query set, induction on digits gives the exact completion H×B, where H is the smallest binary-coordinate subcube containing its slopes and B is its set of intercepts. Consequently each H×B input is exact. ANDing the construction with a singleton-live signal removes all parallel Walsh ghosts, including those induced by an entire affine span, in one physical circuit. It fails on two selected lines (a,b),(c,d) with distinct slopes and distinct intercepts: the completion includes (a,d), with an affine point off both selected lines for q>2. This is a legal singleton-payload negative.
