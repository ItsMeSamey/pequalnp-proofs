# A missing corner forces at least m+n monotone gates

Let M be an m by n Boolean matrix, with distinct row input bits and column input bits. On input (i,j), exactly row bit i and column bit j are true. A fan-in-at-most-two monotone AND/OR circuit must output M(i,j) on these inputs. Size counts gates. Values outside this promise may be arbitrary subject to monotonicity.

Assume the following.

1. No row's set of positive columns is contained in every row's set of positive columns. No column's set of positive rows is contained in every column's set of positive rows. Containment here includes equality.
2. There are distinct rows a,b and distinct columns c,d such that M(a,c)=M(a,d)=M(b,c)=1 and M(b,d)=0.
3. Each of a,b has a zero entry somewhere in its row and each of c,d has a zero entry somewhere in its column. The zero entry can occur outside the displayed four cells.

Then every such circuit has size at least m+n.

## Proof

If a row bit is absent from the output cone, setting that bit alone on the row shore gives the same output as setting no row bit, with any column fixed. Turning on any other row bit can only increase that output. The absent row's positive columns would therefore be contained in every row, contrary to the first hypothesis. The same argument applies to each column. Thus all m+n raw inputs occur in the live output cone.

Let g be the number of live gates. The cone is connected when edge directions are forgotten. It contains at least m+n+g vertices and at most 2g edges, so 2g ≥ m+n+g−1. At equality every gate has two distinct parents, the underlying graph is a tree and each node other than the output feeds just one successor. Indeed every such node has a path to the output, and the tree has only one such undirected path. Extra constant source vertices would preclude equality. Constant gates of fan-in zero likewise preclude equality. Consequently a circuit with at most m+n−1 gates is a binary read-once formula in all the raw bits.

Set all bits except a,b,c,d to false. Eliminate constant subtrees, collapsing their parents as Boolean identities permit. The formula is still read-once. A singleton at any retained bit evaluates to false by monotonicity and the third hypothesis: adding the appropriate opposite bit yields a promised zero. The all-zero assignment is also false. All four variables remain essential, since each belongs to an accepted pair whose other endpoint alone is rejected. Hence the reduced formula has a binary root, with a nonempty disjoint variable set in each child. Both children are built from variables using AND and OR, so each is false on the empty input.

If the root is OR, each child is false on every singleton of its variable set. Every required positive pair must therefore lie in a single child. The three positive pairs connect all four variables, which would put all four into one child.

If the root is AND, every required positive pair must cross the root partition, since a child receiving no active variable is false. The three positive pairs therefore put a,b in one child and c,d in the other. The positive pair (b,c) shows that b alone turns on its child; (a,d) shows that d alone turns on the other. Then (b,d) is accepted, contradicting the specified zero.

This rules out size m+n−1 and proves the bound. The argument never evaluates a same-shore pair as a promised input. A zero corner by itself does not supply the second hypothesis: the other three displayed cells must be ones.

## Exact instance

For m=4, n=6, matrix mask 818815 (bit 6i+j), the rows are 111111, 100111, 111000, 110000. The row intersection is column set {0} and no row equals it. The column intersection is row set {0} and no column equals it. Choose (a,b,c,d)=(2,3,1,2). Both selected rows reject column 3, and both selected columns reject row 1. The theorem gives size at least 10. The ten-gate circuit in check.py achieves equality. Run python3 check.py to verify the hypotheses and the upper bound on all 24 promised inputs.
