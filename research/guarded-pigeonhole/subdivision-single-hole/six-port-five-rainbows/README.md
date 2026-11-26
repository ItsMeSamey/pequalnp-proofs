# Planar bipartite six-pole with five rainbow permutations

Use left vertices A0 through A4, right vertices B0 through B4, and the following internal neighborhoods. Place one tip at each of A0,A1,A2,B0,B1,B2, in that order.

| Vertex | Neighbors |
|---|---|
| A0 | B0, B3 |
| A1 | B1, B3 |
| A2 | B3, B4 |
| A3 | B0, B2, B4 |
| A4 | B1, B2, B4 |

The graph is connected and planar: suppressing the six degree-two vertices produces K4 on B3, B4, A3, A4. No claim about a simultaneous outer face for the tips is needed.

The exact signature contains all nine minority pairings and five rainbow permutations. In common index order the realized output permutations for input 012 are 012, 021, 120, 201 and 210. The missing assignment is 012102. To see its impossibility, the tips on A0,B0 have distinct colors 0,1. Their common edge must have color 2, so B3–A0 has color 1. The tips on A1,B1 similarly force B3–A1 to color 0. Hence B3–A2 must have color 2, which conflicts with the A2 tip. Monochrome tips cannot extend because the three neighbors of B3 each carry a tip of that color.

The standalone checker enumerates boundary colorings modulo a simultaneous permutation of the three colors and enumerates proper colorings on all twelve internal edges. It verifies the fourteen positive orbits and both missing balanced orbits; it also checks all unbalanced orbits. Run python check.py.
