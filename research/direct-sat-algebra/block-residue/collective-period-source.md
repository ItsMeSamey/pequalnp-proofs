# Three incomparable physical bicliques with successive period gains

Use twelve distinct comparison types, allocated by the following table. Every entry represents one separate geometric edge on the named cycle, including entries bearing the same letter in the same cell. Within each row form four physical OR shells, one for every pair of types across its shores.

| Conflict component | Left shore | Right shore |
|---|---|---|
| P | A, B | A, C |
| Q | A, A | B, B |
| R | B, B | C, C |

Build three disjoint simple cycles, of lengths 4, 5 and 3 respectively. Place the occurrences of each letter on successive edges of its cycle in table order, reading left to right within a row. Request difference one on the first A of P-left, the first B of Q-right and the first C of R-right. Request zero on every other edge. Each type appears twice among the indexed shells, giving degree four at every vertex of the indexed comparison multigraph. All its paths under degree-two suppression are therefore singletons. Sharing identical failure types recovers exactly the three displayed conflict components.

For failure bit f_e = x_u XOR x_v XOR d_e, circulation on each geometric cycle requires the XOR of its failures to equal one. Conversely, satisfying each of these three parity equations suffices, by integrating differences along the cycles. Thus each letter contributes its coordinate unit column and the target is (1,1,1).

Initially neither shore span contains its partner in any component. Only P has a nonzero intersection, namely the A direction. After adding A to the global free space, Q has quotient shores zero and B, and fixing its right shore adds B. At that stage P still has quotient shores B and C, and R still has B and C. On the next scan modulo A and B, both P and R have quotient shores zero and C, making C free. The simultaneous closure therefore takes three gain passes and leaves no orientation to enumerate.

An explicit failure support consists of exactly the three target-one edges. It uses P-left, Q-right, R-right, lies in no conflict pair, and is realized by setting every cycle potential to zero. For a literal four-raw-bit implementation give each of the twelve shells a fresh comparison in each position j=0,1 between coordinates 4s+j and 4s+j+2, whose raw request is difference one. For each directed geometric edge u to v with target d, tie its first occurrence endpoint to the potential of u with offset zero, and its second to that of v with offset 1 XOR d, consistently for both copies. No extra raw vertices are needed: for each geometric vertex, tie the raw endpoint occurrences to the first such occurrence by signed copy pins with target equal to the XOR of their two offsets. Each raw bit equal to its own offset then satisfies these pins and realizes the displayed failure support on all 24 indexed comparisons.
