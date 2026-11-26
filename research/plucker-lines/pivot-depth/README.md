# Exact pivot depth for rooted cycle and spectator generators

In a simple bipartite graph, a support is feasible if it contains the two prescribed vertices and induces even degree at every selected vertex. A chart changes coordinates by edge pivots avoiding the roots. A generator in a chart with adjacent roots is an induced cycle containing the root edge, optionally together with one vertex having no neighbor on the cycle. For nonadjacent roots take the independent root pair and independent triples containing it. Pull these generators back to the original coordinates before taking their affine hull over GF(2).

For each integer k≥1 there is a 2-connected bipartite graph of maximum degree four with a vertex marker that first occurs in a generator at **exactly k+1 pivots**. The lower bound allows arbitrary repeated pivots. In particular the affine hull from every chart of depth at most k misses a feasible marked point.

## Construction and unique marked witness

Take three hubs A, B, C, with A and B on the left and C on the right. Use two length-two A–B paths through distinct right vertices T and U. Add direct edges AC and BC, an additional A–C path of length 2k+1, and an additional B–C path B–Z–V–C. All path interiors are disjoint. Pin A and T. Mark the first vertex of the long path after A. The graph has 2k+7 vertices, the hubs have degree four and all other vertices have degree two. Subdividing the edges of a triangle with each side doubled gives this graph. Deleting any hub leaves the other two joined and all remaining path fragments attached. Deleting an internal vertex leaves the surviving hubs connected by alternate paths and the remaining fragments attached. Thus the graph is 2-connected.

The full set is the only feasible support containing the marker. The selected T and A force B. With A and the first vertex of the long path selected, degree two forces every vertex up to C. At C the already-selected neighbors A, B and the final long-path vertex force V, and then V forces Z. At A its three selected neighbors T, C and the marked vertex force U. Conversely the full set is feasible by the degree count. Consequently any affine combination attaining marker one must include a generator equal to this full set in the original coordinates.

## Pivot coordinates and the kernel bound

Let M be the binary adjacency matrix. Pair every coordinate x_i with y_i=(Mx)_i. An edge pivot swaps x_i with y_i at the two endpoints. It preserves feasibility since it preserves each product x_i y_i. The new graph is bipartite with the pivot endpoints exchanging sides. This follows by solving the two swapped equations with the invertible adjacency block on that edge. Coordinates keep their vertex names under the exchange.

After any sequence of pivots, let J consist of the vertices swapped an odd number of times and let R be its complement. On the full witness the initial pair is (all ones, all zeros), so its new support is exactly R. On the entire graph of the linear map M, the final first coordinates are (y_J,x_R) and specify the full state uniquely, since each edge pivot is invertible. Hence M[J,J] is nonsingular. The induced matrix on R is the Schur complement

    M[R,R] + M[R,J] M[J,J]⁻¹ M[J,R].

Indeed set the final first coordinates on J to zero and solve for the original x_J. Restriction to R is therefore an isomorphism from ker M onto the kernel of the induced matrix. It respects the original bipartition on R. In particular it is an isomorphism on right-supported kernel vectors: given a right-supported kernel vector on R, extend it uniquely and split the extension into its original left and right parts. Both are kernel vectors by bipartiteness, and its left part vanishes on R, hence everywhere by injectivity. Every vertex in R is on its original side in the final graph.

The original right-supported kernel consists of all functions constant separately on the classes

- F = {T,U}
- K = {C and all right interior vertices of both additional paths}.

The internal degree-two left vertices along those paths force the K entries to agree. The hub equations at A and B then force T and U to agree. Every such assignment satisfies the equations. Thus |K|=k+2 and restriction to R gives two nonempty kernel classes F∩R and K∩R whose indicator functions are independent.

If the image of the full witness is a root cycle with at most one spectator, the cycle's right-supported kernel consists of its constant functions on the right vertices. To reach dimension two the spectator must exist and be on the right. Its singleton and the right vertices of the cycle are precisely the two classes of vertices indistinguishable by *every* right kernel vector. Since T is on the rooted cycle, F∩R is its right side and K∩R is the singleton. Thus at least k+1 original right vertices have changed sides. Each pivot moves just one current right vertex to the left, so this requires at least k+1 pivots, even with repetitions. In the nonadjacent-root case the image must have at most three vertices. Each pivot can decrease support by at most two, giving the stronger lower bound (2k+7−3)/2=k+2 in that case.

## Attaining the depth

In order from A toward C, pivot on each successive pair of internal vertices of the long A–C path. They are distinct and disjoint from the roots. In the surviving selected graph, eliminating an adjacent pair along that path toggles the edge between its two remaining exterior neighbors. This follows from the displayed Schur complement for a single edge. It shortens the surviving path by two. At the last pair the edge AC cancels the existing direct edge. Calculating on the surviving graph is valid at every step because the Schur update on surviving coordinates uses only their incidences to the current pivot pair.

Now pivot on B,C. The surviving selected vertices are A,V,T,U,Z. Their induced edges are AT, AU, VT and VU: eliminating B,C toggles VT, VU and the existing VZ. The result is the rooted four-cycle A–T–V–U–A together with isolated Z, as required.

## Replay

Run `python3 check.py` in this directory. The independent finite replay checks the unique marked witness directly for k=1 through 5 and enumerates all reachable basis charts in increasing pivot distance for k=1 through 4. It verifies the displayed k+1-step sequence for k=1 through 24. Basis charts are keyed by the set of vertices whose coordinates are swapped; this determines both the transformed graph and the image of the witness by the formulas above.
