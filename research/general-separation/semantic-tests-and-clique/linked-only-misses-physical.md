# Every full link can miss a realizable exterior state

The [nine-site 35-state fixture](single-missing-rank-three-state.md) has three named pins P numbered 0,1,2. Use the natural boundary factorization with their port-color rows equal to the identity. The one missing inner state in this chart is (s,t)=(3,7). Add an unpinned vertex z with the neighbors of pin 2 and no edges to the pins. The ten adjacency masks are

    170,449,240,81,812,853,686,839,178,240.

In the auxiliary exterior the pins are joined to the ports by the identity and z is adjacent only to port 2. Fixing the pin symbols sets the port input to 3, so z has output zero regardless of its input. The two inputs give exactly (3,7) and (3,3). The first is missing and the second present. Original-graph enumeration gives the three witnesses 615,663,967.

Every fully linked labeled pivot/deletion run returns the first state. It clamps one coordinate at each removed site to zero, and these choices give a unique solution for the six fixed pin bits by the [linked-chart argument](linked-scc-port-reduction.md). Clamping the output of z cannot give a unique solution; all linked choices therefore clamp its input to zero. This includes additional edge pivots and swaps at pins or ports, provided the procedure ends on just the six named sites with full cross rank and lifts by zeroing each deleted input.

## Growing highly connected examples

Replace each of the six inner sites by t nonadjacent false twins, preserving complete adjacency on each old edge. This preserves the inner table: reduce a selection to the classes of odd selected multiplicity. Each discarded even class contributed zero parity everywhere, while every selected odd class retains its original degree parity. Conversely choose one copy of each selected old site. Keep the three original pins and their internal edge 0–1.

Add 3t unpinned real exterior sites forming a clique. Assign t each of the following types (R,V), where R is its neighborhood in P and V is its three-bit virtual port neighborhood:

    (0,4), (0,3), (3,7).

A physical site of type V is adjacent to each inner copy whose old pin-neighborhood has odd dot product with V. The pin-to-inner adjacency has rank three. Each site type and pin has an inner neighbor, and the six inner classes have connected base graph. Deleting fewer than t vertices leaves all inner classes occupied and connected, hence the graph is connected after these deletions.

For real exterior inputs z, pins and ports give w=(3,7)+Cz with column types C_i=(R_i,V_i), spanning three dimensions. Each R has even parity, every V·3 vanishes, and every V_i·R_j vanishes. All real outputs equal Hz where H is the zero-diagonal clique adjacency on 3t sites. A fully linked run uses output clamps K, sets all other inputs to zero, and has a unique solution to H[K]z_K=0. It must therefore set every input to zero. In contrast selecting one site of type (0,4) reaches (3,3), giving a physical witness with an inner representative. Deleting all real exterior sites directly realizes a full link. The clique is one SCC of port rank three, invariant across linked charts by the [component theorem](linked-scc-port-reduction.md).

Thus searching all fully linked orientations is incomplete even on YES graphs of unbounded vertex connectivity with a verified 35/36 inner table and an arbitrarily large intrinsically rank-three exterior component. The example has a visible single-site escape; it does not give an algorithmic lower bound or invalidate the [36-state guarantee](rooted-full-boundary-linking.md).
