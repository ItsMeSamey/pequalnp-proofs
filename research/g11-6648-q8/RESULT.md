# G11 original paid-OR count eight

For L-meta-6648, let C be an original circuit of size at most 21 satisfying IsLeastAO, TopForm, and at least three junk ANDs. Assume the issued selections X⊆Ustar and J⊆junk, their cardinality balance |X|+j=|Ustar|+|J|, coverage of X by the selected gamma fibers, exclusion of singleton selected fibers, and a disjoint edge pair in one selected fiber. When q=|orN∖lam|=8, the claimed selected inequality holds.

Write U=|Ustar|, s=16−U, c=|centreless|, P=j+2c+8. By balance it suffices to prove U≤P. The original size floor forces size exactly 21. The zero-, one-, and two-star dispatches in PRIOR.md imply s≥3 under strict failure. Since s≤15−P, the only possible triples (j,c,s) are (3,0,3), (4,0,3), and (3,0,4). All counts concern original physical gates and original starred edges.

## Three starred edges

For four junk ANDs use 6648-q8-j4-three-stars-column.md, including its independent graph-only 5,980-placement replay for the path-plus-edge case. For three junk ANDs at q=8 (also at 4≤q≤7), dispatch as follows.

* Triangle, claw or four-vertex path: at least seven exterior labels with cover number at least three; P=q+3≤11. Thus P−|O|≤4 and 6648-exterior-cover-small-slack.md excludes the circuit. This proof directly covers the lower budget.
* Two-edge path plus a separate edge: twin_6648_q4_9_p3_k2.md already treats original 4≤q≤9.
* Three-edge matching: 6648-three-matching-lower-q.md uses the original size count 2t+λ=19−q≥11, the q-dependent raw reader reservation, and the endpoint multiplicities to force 2t+λ≤10.

## Four starred edges and three junk ANDs

Classify by the number of incident vertices. The C4-free condition excludes a four-cycle. A connected acyclic component is a tree; the only cyclic component with at most four edges contains a triangle. Partitioning four edges over connected components gives precisely the following shapes.

| Endpoints | Shape | Source |
|---|---|---|
| 4 | Triangle with pendant edge | Seven exterior labels and six dirty pins force seven proper exterior unions by 6648-global-exterior-thresholds.md. The exterior has an edge because an independent exterior would give a four-label cover. Its winning ordinary top requires two additional distinct dirty entrances on opposite sides, since a shared donor would transmit an original independent witness. Thus q≥9. |
| 5 | Four-leaf star | 6648-q8-four-leaf-star.md |
| 5 | Five-vertex path | twin_6648_q8_five_path.md |
| 5 | Fork with degree sequence 3,2,1,1,1 | 6648-four-star-fork-all-readers.md |
| 5 | Triangle plus a separate edge | encoding_6648_q8_triangle_edge_complete.md and 6648-q8-triangle-edge-two-mandatory.md |
| 6 | Two disjoint two-edge paths | twin_6648_q8_two_wedges.md |
| 6 | Four-vertex path plus a separate edge | twin_6648_q8_path_edge.md and twin_6648_q8_path_edge_completion.md |
| 6 | Three-leaf star plus a separate edge | 6648-hub-pair-all-readers.md |
| 7 | Two-edge path plus two separate edges | 6648-q8-wedge-two-matched.md, 6648-q8-wedge-m4-bare-closure.md, 6648-q8-wedge-five-import-controls.md and 6648-q8-wedge-five-import-closure.md |
| 8 | Four-edge matching | twin_6648_four_matching_three_junk.md |

These arguments exclude all original signatures needed under strict failure. The resulting research statement concerns q=8 only. This is a source synthesis. Independent cell and archive reviews are tracked separately. No combined Lean receipt is supplied.
