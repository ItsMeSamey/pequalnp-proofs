# Five paired products require at least 174 gates in the retained circuit

## Circuit class

Start with the 16 AND products of the 180-gate circuit in `context.json`, numbered from zero in gate order. Retain all except products 7, 10, 11, 12 and 13. Retain the positive OR ancestors of the eleven fixed operand pairs and of marker input wire 121. This costs 114 OR gates. The available bank consists of these gate outputs and the 64 row and column input atoms. Charge one NOT on the marker input for shard 53. Its output is unused by the products.

Each of the five replacement products is a binary AND of two endpoints. Build the ten endpoints from the bank by binary ORs, allowing arbitrary sharing. The circuit joins the sixteen products by fifteen binary ORs. The endpoint, product and output stages are charged separately. We prove a lower bound for this topology on the 1,024 legal one-row, one-column inputs.

## From products to pairs of rectangles

Write the support of an endpoint as a set of row atoms and a set of column atoms. On cell $(u,v)$ an endpoint with support $(A,B)$ is true if $u\in A$ or $v\in B$. If this endpoint is paired with $(C,D)$, their AND includes every cell in rows $A\cap C$ and every cell in columns $B\cap D$. Each row and each column of the target has a zero. Since the output OR preserves every positive produced by a product, both intersections must be empty. Expansion of the AND then leaves precisely the two rectangles $A\times D$ and $C\times B$.

Let $U$ be the 98 target cells uncovered by the eleven fixed products. The following ten cells of $U$ form a packing, in zero-based row and column coordinates.

```text
(19,14) (31,28) (0,19) (5,27) (26,5)
(17,3)  (21,22) (23,1) (18,18) (2,17)
```

For each pair, at least one cross cell is zero in the target. An all-one rectangle can therefore contain at most one packing cell. The five products yield at most ten rectangles and must cover all ten packing cells. Hence each rectangle contains a distinct packing cell.

Extend each rectangle to any inclusion-maximal all-one rectangle of the target. These ten parents remain distinct by the same packing argument, and their union covers $U$. The exhaustive enumeration gives 214 parent covers. One way to reproduce the enumeration is to intersect nonempty subsets of row neighborhoods, retaining distinct nonempty intersections. For each intersection take all rows containing it. These are exactly the maximal all-one rectangles, since maximality forces both the column intersection and the full set of rows containing it. Choose one parent containing each packing cell and retain the tuples whose union covers $U$. Every actual circuit occurs among these tuples with its rectangles trimmed inside the chosen parents. The five products specify a perfect matching of the ten parents. There are $9\cdot7\cdot5\cdot3\cdot1=945$ matchings per tuple.

## Forced atoms and private gates

Write parent $i$ as $R_i\times C_i$. Take the cells of $U$ covered by parent $i$ alone among the ten. Write $r_i,c_i$ for their row and column projections. Every feasible trimming must keep all these rows and columns in rectangle $i$. Thus a matched pair $i,j$ with overlapping forced rows or overlapping forced columns is impossible. For a surviving pair the two endpoints have allowed supports
$A_{ij}=R_i\sqcup C_j$ and $A_{ji}=R_j\sqcup C_i$, where the disjoint union tags row and column atoms. Their mandatory supports are $M_{ij}=r_i\sqcup c_j$ and $M_{ji}=r_j\sqcup c_i$. Each actual endpoint support lies between its mandatory and allowed sets. This permits arbitrary further trimming.

Index the ten endpoints by $e$. For endpoint $e$, grant every bank support contained in $A_e$ and every intersection $A_e\cap A_f$ for another endpoint $f$ at zero additional cost. Let $d_e$ be the fewest granted pieces whose union contains $M_e$. To see why this bounds gate cost, trace the endpoint backwards through new OR gates. Stop at a bank wire or at a new gate that reaches a second endpoint. Every wire reached has support contained in $A_e$ by monotonicity of OR. A gate shared with $f$ also has support contained in $A_f$. Its entire contribution thus fits inside one granted intersection. The frontier wires cover $M_e$, so there are at least $d_e$ distinct frontier wires. All internal gates in this traced subgraph are private to $e$. If it contains $p$ private gates and $h$ frontier wires, connectivity requires at least $p+h-1$ edges while binary fan-in allows at most $2p$. Consequently $p\ge\max(0,d_e-1)$. The private gates for different endpoints are disjoint, so their lower bounds add even in a circuit with unrestricted OR sharing.

For finite evaluation, intersect the granted pieces with $M_e$ and discard empty or dominated pieces. On an uncovered set $S$, choose any atom $x\in S$. The minimum piece count is one plus the least remaining count on $S\setminus P$ over pieces $P$ containing $x$, with count zero on the empty set. This computes each $d_e$ exactly for the relaxation.

Of the $214\times945=202{,}230$ parent-cover and matching combinations, forced overlaps exclude 196,530. Among the remaining 5,700 the smallest sum of private-gate bounds is 28. Eight combinations reach that relaxed minimum. The resulting circuit lower bound is **114 + 16 + 15 + 1 + 28 = 174 gates**. Granting shared intersections at zero cost can underestimate implementation cost, so attainment at 174 remains unproved. The unrestricted existence of a 170-gate circuit for this graph lies outside the theorem.
