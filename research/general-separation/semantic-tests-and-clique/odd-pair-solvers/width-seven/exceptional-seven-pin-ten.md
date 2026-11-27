# The exceptional degree-seven child has exactly ten sites

Consider an inclusion-minimal finite simple induced all-odd support H with two distinguished sites q,r. Suppose q has degree three, r has degree seven, N(q)⊆N(r), and all other degrees are at most five, measured in H. Then H has exactly ten sites. Examples exist both with and without an optional leaf.

The names are nonadjacent. The full support is connected: any component lacking a name could be dropped, while two separate named components could be replaced by one edge at each name. The [high-pin leaf bound](high-pins-forbid-two-optional-leaves.md) allows at most one leaf. The root consists of both names, three common neighbors C and four r-exclusive neighbors B. No common neighbor touches the exterior: the two names, that common neighbor and its exterior neighbor would form a proper induced claw. Thus each C vertex already has final degree three or five at the root. Every possible remaining edge in B∪C is enumerated, respecting the nonpin cap five. The root has nine vertices, so cannot itself be all odd.

The [exceptional-root checker](exceptional_seven_pin_shells.py) uses the independently checked [single-leaf shell transfer](single-leaf-high-pins-eight.md) with exactly zero and exactly one degree-one budget in separate runs. Neither pin is a frontier vertex. All exposed or newly added sites therefore obey precisely the old bounds. The checker makes no connectivity or minimum-interface-size pruning, retains physical graph histories, and tests each accepted graph on all proper subsets containing both pins.

| Layers after the root | Physical prefixes per budget | Distinct budgeted tables per budget | Accepted with a terminal layer, per budget |
|---:|---:|---:|---:|
| 0 | 107856 | 7020 | 576, all order ten |
| 1 | 4464 | 32 | 0 |
| 2 | 8640 | 30 | 0 |
| 3 | 4608 | 14 | 0 |
| 4 | 0 | 0 | 0 |

The two budgets give the same counts with different accepting graphs. With pins 0,1 in order of increasing degree, examples in adjacency-mask notation are (448,508,770,386,546,914,131,107,47,52) without a leaf and (448,508,386,546,290,26,259,7,87,8) with a leaf. Counts use fixed labels inside B and C and are not isomorphism counts.

In the named-leaf elimination that removes two vertices and toggles the edges from the transferred pin r to a three-element set C=N(q), its only possible new degree above five is seven: the old r must have had degree five, no neighbors in C, and lost one old neighbor. The transformed q still sees exactly C, all three now adjacent to r. If the transformed full word is inclusion-minimal under the exact elimination, the theorem bounds this original branch by twelve vertices. The proof uses the actual selected support throughout.
