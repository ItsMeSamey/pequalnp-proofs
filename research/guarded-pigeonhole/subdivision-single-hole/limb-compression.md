# Boundary-preserving compression of bipartite cubic limbs to seven vertices

A limb is a connected bipartite induced region of a loopless cubic multigraph, counting both named original dangling ends and all cut edges to the exterior as its k boundary ends. The exterior need not be bipartite. For k≤5 there is an actual bipartite cubic multipole with the same labeled boundary extension relation and at most seven internal vertices. The reduction preserves decision and reconstructs an original coloring. It need not preserve the number of completions or a prescribed disk embedding.

## Bridgeless pieces

Let A be a shore carrying at least as many ends as B. Proper boundary colors satisfy, for each color c,

    number of c ends on A − number of c ends on B = |A|−|B|.

All counts include multiplicities. In a connected bridgeless internal graph with at least two vertices every holder has at most one end, since internal degree one gives a bridge. A singleton has three ends and its balanced tuples have all three colors distinct. Choose a most frequent color c. For k>0 the possible balanced multiplicities, disregarding zeros and permutations, are (2), (1,1,1), (4), (2,2), (3,1,1). The A:B shore counts of all ends are respectively 1:1, 3:0, 2:2, 2:2, 4:1. These follow by summing the three color balances. Boundary width one cannot occur.

Let A_c,B_c denote the holders of c. We need a perfect matching after deleting those holders. The remaining shores have equal size. If Hall fails on the remaining A shore, choose a deficient nonempty X there and put Y=N(X) in the *original* graph. Then |Y|−|X|≤|Y∩B_c|−1. Every edge out of X∪Y goes from Y to A outside X. Writing t for the number of boundary ends on its argument, the cut size is

    3(|Y|−|X|)+t(X)−t(Y) ≤ 2|B_c|−3+(number of non-c ends on A).

In the five listed cases the right side equals −1, −1, 1, 0 and 1, respectively. The nonempty set X∪Y is proper since A_c is nonempty. A cut of size at most one contradicts connected bridgelessness. The singleton was treated separately. Thus a c-matching exists. At most two non-c ends remain, so the residual even cycles and paths admit the prescribed two other colors by alternating along them; this is the two-terminal argument of matching-multipole.md. A zero-boundary cubic bipartite piece colors by perfect-matching decomposition. Consequently the balance equations suffice on every bridgeless piece of width at most five.

Representatives by boundary count are: for 0 use two vertices joined by three edges; for 2 use two vertices with a double internal edge and an end each; for 3 use one vertex with three ends; for 4 use a four-cycle with one end per vertex; for 5 start from a triangle with multiplicities 1,1,2, separately subdivide its four edges, and put ends at the four new vertices and the unique degree-two original vertex. For each piece choose any bijection preserving terminal shores up to simultaneous reversal. Identified holders in the 3-representative cause no extra constraint since the balanced patterns are rainbow. The numbers of labeled boundary tuples are respectively 1,3,6,15,36.

## Arbitrary bridges and size bound

Remove all internal bridges to obtain a tree of bridgeless pieces, counting each end of a bridge as a local boundary incidence. In a colorable limb every branch at a bridge must contain some original end of the limb: otherwise the xor of the three nonzero colors at every vertex on that branch sums to zero but only the nonzero bridge color crosses. Indeed a terminal-free bridge shore is impossible in a bipartite cubic input already by the degree imbalance modulo three. At each node its incident branches are disjoint and each consumes at least one such end. Thus the total local arity (its own ends plus tree degree) is at most k.

Replace each piece by the corresponding representative. A local 2-pole transmits equality between its two ends, placed on opposite shores. Suppress every such piece. A chain connecting two retained pieces becomes one edge. A chain ending at a named terminal moves that same terminal label to the retained piece, preserving its shore because the equality piece and its outgoing bridge each reverse the shore. If k=2 all pieces are of arity two and the whole limb is a single 2-representative. Zero ends are handled separately. Otherwise every retained piece has arity j between three and five; its representative uses 3j−8 vertices. The tree on b retained pieces has total arity k+2(b−1), so the constructed limb uses exactly 3k−6−2b≤3k−8 vertices. This gives bounds 1,4,7 for k=3,4,5. The constructed bound does not assert minimum representative size for every signature.

## Finding regions and lifting original witnesses

Enumerate ordinary edge sets of size at most five, remove them, and inspect each connected component S. Test bipartiteness and compute the full actual boundary by inspecting all original cuts and named ends. Every eligible region is seen when its own cut is removed. Apply a substitution only when its vertex count strictly falls, then restart the enumeration. The number of accepted steps is linear in the original vertex count. This is polynomial time for the fixed threshold five; enumerating fifth-order cuts can still be expensive. At termination there is no eligible limb larger than its constructed representative. This gives no bound on the order of an arbitrary remaining core.

Store the original induced region, named end indices, surviving cut-edge identifiers and new internal edge identifiers. Given a valid colored reduced core, process this stack in reverse. Solve the stored original bipartite multipole at its now known boundary with the one-matching algorithm, copy its keyed edge colors, and drop the new representative's internal colors. The exact boundary relation guarantees success. Verify the final original incidences. Exterior constraints involving only original terminal labels retain their meaning.

The checker compares 1,900 labeled patterns on 16 small simple multipoles against an independent edge-color enumeration. It verifies the five representatives, shrinks a 24-vertex bridge chain to two vertices, reverses two strict substitutions around a nonbipartite K4 core, and checks all 243 boundary assignments on a 17-to-7 replacement that moves five named tips. The implementation uses keyed loopless multigraphs and integer vertex identifiers.
