# A physical refactoring bound with external taps

In a binary monotone DAG choose upstream row signals G_x and column signals u_i,Y_i outside a bank. Bank gates consist of A_xi=G_x∨u_i, B_xi=A_xi∧Y_i, and same-row ORs of products or other same-row ORs. Each such OR represents a nonempty index set J; operands may overlap. A tap is any bank node read outside the bank, including the scalar output if in the bank. Count distinct tapped nodes irrespective of fanout. A tapped product has J={i}.

Let K count all bank gates, a the number of tapped A nodes, and t the number of other tapped nodes. Choose any shared binary union DAG generating the index sets of those t taps from h singleton indices, with c union nodes. In a gate-minimum representation,

K ≤ a+2t+h+2c.

For each used i compute T_i=u_i∧Y_i. At each union node combine the two Y values by OR and the two T values by OR. Recreate tapped A nodes with one gate each. Recreate every other tap in row x on set J as (G_x∧Y_J)∨T_J, using distributivity. Redirect every outgoing physical slot to its corresponding replacement and delete all K original bank gates. The shared library costs h+2c, independent of tap fanout. All outside outputs retain their values on the full cube. The new program is acyclic because the bank input signals were upstream.

For m full private rows of k columns with distinct A,B and k−1 row OR gates per row, K=m(3k−1), and replacement costs at most 2m+3k−2. Even if ALL A and B gates have outside readers, keep them. If only the m roots of the row OR trees are tapped among the row OR gates, the refactoring still eliminates m(k−1) gates at cost 2m+3k−2. A gate minimum cannot contain this pattern if m(k−3)>3k−2.

This rules out the private collector pattern in the simultaneous high-rank affine controls by an exact physical edit. Distinct interior tap sets may make c large, and no such bank is guaranteed in arbitrary circuits.
