# Large fanout on signals varying on every cofinal family

Choose distinct points p,r. Let a_1,...,a_t,d_p be distinct lines through p avoiding r and b_1,...,b_t,d_r distinct lines through r avoiding p. Initially retain only these lines and these two points. Use t≥2 and define

    g = p OR r,     u = p OR d_r,     v = r OR d_p,
    A_1 = a_1 OR (r AND d_r),         B_2 = b_2 OR (p AND d_p).

Other A_i equal a_i, and other B_i equal b_i. Take the OR of t four-factor terms

    g AND (u OR B_i) AND (A_i OR v) AND (A_i OR B_i).

Each term receives g, u and v on separate wires, giving each shared gate fanout t. These are the only shared internal nodes. Without either donor flag r d_r or p d_p, when g holds the signals u and v behave as p and r: if p is absent then r is present and hence d_r is absent, and symmetrically for v. The four clauses then compute p a_i OR r b_i. On r d_r block 1 fires; on p d_p block 2 fires. Thus the formula after expanding the shared gates computes exactly the induced incidence predicate. Size is 7t+6 and the two hub raws have three uses each.

Every cofinal family of independent assignments makes all of g,u,v variable. Each is forced high by one singleton. To force g low take the two lines a_1,b_1. To force u low take r,a_1; to force v low take p,b_1. These are independent, and every independent extension still rejects the designated signal. This argument holds equally in the full plane. The family need only cover those small tests.

Each occurrence of g is necessary in its own term on the negative a_i,b_i with no points. The remaining clauses are uniquely false, respectively, on r,a_i; p,b_i; and p,r. For either of the first two literal-ORs the ordinary private flags distinguish the operands; for the last OR the same two ordinary flags do so. Gate u needs d_r on donor r,d_r, and needs p on ordinary p,a_i. Similarly v needs d_p and r. Both inputs to g are necessary on ordinary flags. Replacing the donor product r AND d_r with r accepts p,r and replacing it with d_r accepts p,d_r. Its attached OR needs both ordinary and donor flags. The symmetric checks apply to p AND d_p. These facts also cover bypass at intermediate nodes of the binary AND aggregation. Thus local parent-bypass normalization does not dispose of the high-fanout signals. They can still be removed by a coordinated rewrite into the two ordinary stars.

For a balanced instance choose 2≤t≤q/10 in PG(2,q) with odd q. Add t isolated matching flags selected from conic points and tangents, omitting points on any retained line (at most 4t+4) and tangents through either hub (at most four). Add 2t extra points on d_r meeting no other selected line; the b_i meet d_r only at r and the other retained or matched lines exclude at most 2t+2 points altogether. Add the extra d_r-star output and matching outputs by OR. There are N=3t+2 variables per shore and s=11t+7 gates, below 4N. The original witness masks, including all small cofinal tests, retain their evaluations. This is an induced restriction and has many degree-one vertices. Adding the other plane flags yields an exact full-plane circuit, with no corresponding full-plane 4N upper bound.
