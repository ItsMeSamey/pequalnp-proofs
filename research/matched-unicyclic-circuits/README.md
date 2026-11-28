# Exact monotone circuit size for matched bipartite graphs with at most one cycle

Let G be a finite simple bipartite graph with a perfect matching of n≥1 edges and m edges in total. Assume the entire graph has at most one cycle and contains no four-cycle. The minimum size of a binary monotone circuit computing its edge function is **m+n−1**. Every such circuit uses at least **m−1 OR gates** and at least **n AND gates**. One circuit attains both counts simultaneously.

This covers a forest, or an even cycle of length at least six with arbitrary attached trees and separate forest components, provided the final graph has a perfect matching. For connected unicyclic G there are 2n vertices and m=2n, hence the exact size is 3n−1.

## Circuit and graph conventions

There is one unconstrained Boolean input for each vertex. The output must equal one exactly when the active vertices contain both endpoints of some edge. The requirement holds on all Boolean assignments, including assignments activating multiple vertices in either part. The circuit is a straight-line list of AND and OR gates. Each gate has exactly two earlier operands, possibly repeated. Inputs and fanout are free. The output may name any existing wire. Each physical gate in the list costs one regardless of fanout. Input and output wires are uncomplemented. Restriction arguments propagate constants and remove aliases in a proof; the constructed circuit uses only the specified binary operations.

## Lower bound

The [lower-bound proof](lower-bound.md) first proves that the edge function of a bare cycle of length h≥5 requires h−1 OR gates, and that length 2k≥6 requires k AND gates. The first gate of the counted type isolates a set of raw inputs if every single-vertex restriction can eliminate only one such gate. A nontrivial isolated set contradicts the cycle's distinct neighborhoods. The proof then charges off-cycle OR gates by pinning leaves to zero. For AND gates it pins a matched leaf to one and its unique mate to zero. These are independent lower bounds on disjoint classes of gates in the original circuit. A forest needs m−1 OR gates by leaf removal and n AND gates by matched-pair removal.

## Matching upper bound

A perfect matching makes each bipartition class have n vertices and leaves every vertex incident with at least one edge. Use the left class as centers. For each left vertex u, OR together its right-neighbor inputs, using deg(u)−1 OR gates. When u has one neighbor this signal is the raw neighbor input. Take its AND with the input for u. Finally OR the n center outputs together with n−1 binary ORs. Each edge term occurs at its left endpoint, so the circuit computes the edge function on every assignment. The total is n ANDs and

    Σ(left vertices u) (deg(u)−1) + (n−1) = (m−n)+(n−1) = m−1 ORs.

## Two eight-vertex examples

Start with the cycle (0,1,2,3,4,5,0). Attach leaf 6 at vertex 0. Attach leaf 7 at vertex 1 in the adjacent example and at vertex 3 in the opposite example. Both graphs have m=8 and n=4, so the minimum is eleven gates, with seven ORs and four ANDs. Perfect matchings are respectively {(0,6),(1,7),(2,3),(4,5)} and {(0,6),(3,7),(1,2),(4,5)}. The distance between the two degree-three vertices on the unique cycle distinguishes the two graphs.

## Status and scope

This is a mathematical research result. The elementary argument is independent of a Lean compilation. The issued statement L-meta-8577 also permits connected graphs with more than one cycle. Its general case remains outside this theorem.
