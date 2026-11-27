# Relative potentials at branch vertices

Consider an explicitly indexed undirected comparison multigraph. Each edge e requests x_u XOR x_v = t_e, and each indexed edge belongs to one pair. Each pair requires at least one of its requests to hold. Parallel edges and loops retain separate indices. The following bound concerns decision and witness recovery.

Treat loops as individual blocks and a pair of parallel edges as a cycle of length two. Call a block balanced if its edge requests can all hold simultaneously. For every unbalanced block B that is not a simple cycle or single loop, let b_B count its vertices of degree at least three **within B**. Set k equal to the sum of b_B − 1 over these blocks. Decision and witness recovery take at most 2^k calls to the balanced-block and simple-cycle solver, with polynomial overhead per call and polynomial space.

## Identifications and lifts

Compute the block decomposition and test balance within each block by propagation. Both steps together take linear time in the explicit graph. In each selected block choose one branch vertex as root. For every other branch vertex in that block, enumerate its potential relative to the root. The resulting k binary equations form a forest. Indeed, each block contributes a star, and rooting the block-cut forest shows that each new star can share at most one vertex with earlier stars. This remains true when intervening blocks contribute no equations.

In a branch, record the representative R(v) and offset h(v) of each vertex under these equations. An assignment to representative potentials lifts by x_v = z_R(v) XOR h(v). Rewrite each edge request with endpoints R(u), R(v) and target t_e XOR h(u) XOR h(v). Preserve the edge index and the original pair even if the two endpoints coincide. A loop now has constant truth value. The substitution is a bijection between representative assignments and assignments realizing this branch. Every original assignment determines its branch uniquely. Saved offsets from any earlier copy contractions compose with this substitution.

## Why every quotient is supported

A selected block is connected, has minimum degree two and has a branch vertex. Following edges through degree-two vertices partitions its edges into paths whose ends are branch vertices and whose interiors are disjoint. A degree-two cycle disjoint from all branch vertices would be an entire connected component. Identifying all branch vertices in this block closes each path into a cycle, including a loop when the path consists of one edge. The cycles share only the identified vertex.

Construct the quotient block by block in rooted block-cut order. A new block attaches to the previous union at at most one vertex, including after the identifications within the new block. Thus it introduces no cycle using edges of both pieces, and external identifications cannot merge two vertices of an unselected block. Its edge targets change only by vertex offsets, which preserve balance. Every residual block is therefore balanced, a simple cycle, or a singleton loop.

Start the residual solver with all requests marked satisfied. Each unbalanced cycle requires at least one failed request. A pair can absorb at most one failure. Consequently a satisfying assignment gives a matching from all unbalanced cycles to distinct pairs incident with them. Conversely, for a covering matching, mark one incident edge failed for each matched cycle. All cycle equations now have consistent parity, including those of loops, and the unchanged balanced blocks are consistent. Propagation reconstructs representative potentials. Lifting them recovers an original witness. Failure in all branches proves unsatisfiability. This matching argument supplies no counting algorithm.

## Scope of the exponent

For cycle rank m_B − n_B + 1 = μ_B, summing degree minus two gives b_B ≤ 2μ_B − 2. Subdividing edges adds no branch vertices. In particular an entire unbalanced theta block costs one bit regardless of the lengths of its three paths. A theta embedded in a larger block can have additional edges attached to its interior. Identifying its two poles alone need not make that block eligible. The bound charges every branch vertex of the whole selected block and assumes no efficient search for a smaller cover. Arbitrary signed multigraph cores survive subdivision, and k can be linear in the size of a core, as in an unbalanced cubic 2-connected graph. The result gives no uniform subexponential bound.
