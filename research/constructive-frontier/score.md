# Score definitions

For each AND gate, its raw side is the set of input vertices reached from that operand along OR-only paths. A top is a clean AND. Its star edges are the unordered pairs across the two raw sides. Ustar comprises graph edges absent from all such pairs. A top is centreless if one raw side is empty. Junk comprises dirty AND gates. Lambda comprises dirty OR gates with both raw operand supports nonempty that lie on an OR-only path to a top operand whose opposite side reaches exactly one raw vertex.

Writing t, c, j, o, and l for the numbers of tops, centreless tops, junk ANDs, dirty ORs and Lambda members, Q = t+c+j+o−l. The discrepancy is D = τ+|Ustar|−Q, where τ is the minimum vertex-cover size. The checker evaluates cleanliness over the complete Boolean cube. A reader is counted once even when both its pins read the same gate.
