# Width-four matching-component composition and the Pappus control

The input to composer.decide is a simple bipartite free graph H, its supplied shore function (zero or one), and its external half-edges with fixed blue/green colors. The total degree including half-edges is three at each vertex. Internal red edges must form a perfect matching. For a graph cut at three marked edges, a chosen red mark deletes its two holders: enumerate which of each holder's two remaining incident edges is blue (the other must be green). The other two marks supply their prescribed nonred colors at their free ends. The Pappus marks are disjoint and induced, so all eight resulting half-edges meet free vertices.

Keep the internal edges belonging to some perfect matching, found by forcing edges individually. Connected components of the allowed graph have independent matching choices. Every other edge becomes a blue/green wire directed from shore zero to shore one. The quotient is acyclic: for a fixed perfect matching orient matching edges backwards and nonmatching edges forwards. Contract the matching edges; an optional edge lies on an alternating cycle exactly when its endpoints belong to the same strongly connected component. These are precisely the connected matching-covered components. Topological ordering therefore processes all upstream wires first.

Given fixed external colors, store the bits on the outgoing wires of a processed prefix. Since each allowed block is shore-balanced, edge counting in the cubic completion gives
`outgoing = external_shore_one(prefix) - external_shore_zero(prefix)`.
There are no incoming wires into a topological prefix. Thus at most four outgoing wires and sixteen bit states suffice for at most four external ports per shore. In each block, enumerate outgoing colors, retaining an assignment iff the full local boundary extends. Distinguish a certainly extendible state from one requiring an unresolved local table entry. At termination a definite accepting chain yields SAT, failure even under optimistic entries yields UNSAT, and the remainder yield UNKNOWN.

The sibling matching_multipole.solve decides local balanced blue/green patterns exactly whenever the less frequent color occurs at most twice: match the majority color by a single maximum matching and alternate along the residual paths and cycles. Since each color occurs equally often on both shores, this covers every pattern at most six ports and all eight-port patterns except four of each color. The code also tests the exact two possible red matchings for a cycle block. More general exact local response oracles can be supplied in place of table_entry. The bound on local ports follows from the same prefix count: incoming wires consume at most the number of previously seen shore-one external ports, so incoming plus current shore-one external ports never exceeds four. The two sides of every block have equal numbers of ports.

## Reproducible Pappus example

Use NetworkX's pappus_graph() and marks (0,1), (10,11), (14,15). Cutting all three yields a six-pole realizing all nine paired minority patterns and the monochrome pattern. No named proper coloring gives three distinct colors to the marks. For each red choice, the allowed free graph consists of two disjoint C8 blocks with four red matching products. In each product the other marks occupy the same even cycle and have the same alternating phase. The color-state DP certifies failure for all four orientations at the red holders for each red choice. Independent full-graph enumeration counts 120 named proper colorings. Exhaustive bipartition cuts verify cyclic edge connectivity six, achieved at shore {0,1,2,3,4,5}.

The edge-color LP for this impossible rainbow assignment is feasible. In lexicographic order of the sorted endpoint pairs, the following triples are twice the edge color variables, with columns ordered by the three marked-edge colors.

```
200 011 011 011 011 110 101 011 101 101 110 110 011 101
101 110 110 101 011 020 101 011 110 110 002 110 101
```

The checker validates all edge sums and vertex-color sums, nonnegativity and the three prescribed unit coordinates. Run python check.py with NetworkX and the sibling subdivision-single-hole/matching_multipole.py available.
