# Exact criterion for attaining the physical input-dependence bound

Let M be a nonconstant Boolean m by n matrix with m,n positive. Exactly one row bit and one column bit are active on each promised input. A circuit must output the corresponding matrix entry using fan-in-at-most-two monotone AND and OR gates. Raw inputs are free and gates may have arbitrary fanout.

A row is called minimum if its set of positive columns equals the intersection of the positive-column sets of all rows. Define minimum columns symmetrically. Minimum profiles need not occur as rows or columns. Let d be the number of nonminimum rows plus the number of nonminimum columns. Remove every all-one row and all-one column from the bipartite graph of positive cells; discard isolated vertices from the result.

**The minimum gate count is d−1 if and only if every remaining connected component is complete bipartite. If some component is incomplete, at least d gates are required.** The condition includes the empty graph. In particular, if neither shore contains a minimum vertex, the two bounds become m+n−1 and m+n.

## Physical dependence

If a row bit is absent from the live output cone, its positive-column set is contained in every row's. With any fixed column, activating the absent row yields the same output as activating no row, and turning on any other row can only increase it. This makes the absent row minimum. The column argument is identical. Every circuit therefore reads at least d distinct raw bits. Conversely, all minimum bits can be omitted simultaneously: universal flags and the ordinary edge-by-edge monotone disjunction on the residual graph suffice by the construction below, using individual edge terms in place of component terms if needed.

The matrix is nonconstant, so d≥1. Indeed d=0 would mean all row profiles are identical and all column profiles are identical, forcing a constant matrix. For a connected live output cone with g gates and at least d raw inputs, the distinct edge count is at least d+g−1 and at most 2g. Thus g≥d−1. Equality forces exactly d raw inputs and a tree with two distinct parents at every gate. Every node except the output has precisely one live consumer because there is only one undirected path to the output. The resulting circuit is a read-once binary formula. This also covers d=1 with output a raw bit. Additional constant sources or unary gates cannot improve the bound.

## Construction

The intersection of all row profiles is precisely the set of universal columns. Thus a nonuniversal row is isolated after deletion of universal vertices exactly when it is a minimum row. The analogous statement holds for columns. A universal vertex of a nonconstant matrix cannot also be minimum: all profiles on its shore would then be universal. Consequently the d nonminimum inputs consist precisely of the universal flags and the nonisolated residual vertices.

For each residual complete bipartite component, take the AND of the OR of its row flags and the OR of its column flags. Combine all component outputs and all universal flags by OR. Interpret any single-term OR as that term alone. At least one term exists because M has a positive cell. The formula accepts every cell with a universal endpoint and exactly the residual edges otherwise. Each of the d raw bits occurs once, so the gate count is d−1. If no edges survive, the formula is the OR of the universal flags alone.

## Incomplete component

Choose nonadjacent opposite-shore vertices in an incomplete connected component. A shortest path between them has at least three edges. Its first four vertices induce a path, since an edge from the first vertex to the fourth would shorten it. This gives two rows and two columns with exactly three positive cross-pairs. All four vertices are nonuniversal, so each has a rejecting neighbor somewhere in the original opposite shore. Monotonicity implies all four singleton inputs are false.

In any purported read-once formula, set every other bit to false, including optional minimum bits, then simplify constants. All four variables remain essential because each participates in a positive pair whose other endpoint alone is false. The simplified root therefore has disjoint nonempty sets of variables in its children. Both children are false on the empty input.

If the root is OR, each child rejects every singleton. Each positive pair must have both endpoints in one child. Connectivity then puts the entire path in one child, a contradiction. If the root is AND, every positive edge spans the root split because a child with no active variable rejects. The unique path bipartition puts the rows in one child and columns in the other. Every endpoint activates its own child alone, as witnessed by a required positive pair. The missing corner is then accepted. This excludes every read-once formula, regardless of its treatment of optional bits, and therefore excludes size d−1. No values on same-shore pairs are assumed.

## Instance

Mask 818815, with bit 6i+j denoting cell (i,j), has rows 111111, 100111, 111000, 110000. Universal row 0 and universal column 0 do not realize minimum profiles; neither shore contains a minimum vertex. Thus d=10. Rows 2,3 and columns 1,2 give a residual three-one corner. The matching ten-gate circuit and all 24 input checks are included in the companion missing-corner certificate.
