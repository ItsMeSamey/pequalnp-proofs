# A residual separator of size at most 33 needs at least twenty mixed gates

For the pinned L-meta-18968 samples, let P and L count distinct pure point and line wires entering the connected mixed output cone. Each mixed binary gate uses two operands. If m is the number of mixed gates and k counts uses beyond the first for these boundary wires and the other mixed wires, then m=P+L−1+k. The earlier lower bounds give m≥19, P≥11 and L≥7. At P=11 the exact minimum point cost is **nine gates**, so m=19 leaves at most five line gates. [Prior bounds](../README.md) · [Point costs and proof traces](../point-pareto/README.md)

| P | L | k | Exclusion |
|---:|---:|---:|---|
| 11 | 7 | 2 | [Seven-line two-surplus classification](../two-surplus/README.md) |
| 12 | 7 | 1 | [Seven-line one-surplus classification](../one-surplus/README.md) |
| 13 | 7 | 0 | [Seven-line read-once theorem](../one-surplus/read_once_guards.md) |
| 12 | 8 | 0 | [Eight-line read-once theorem](../eighth_line_good.md), [remaining signatures](../eighth_line_concurrent.md), and [repeated line](../repeated_line.md) |
| 11 | 8 | 1 | Eight-line cases below |
| 11 | 9 | 0 | Nine-line cases below |

## Eight line wires and one surplus use

The eight-slot cover contains all seven singleton labels and an extra signature. Lowering each pure line wire to the OR of its singleton signature preserves the positive rows and can only lower negative outputs. Empty or duplicate signatures reduce to earlier cases. A repeated point input unfolds to the eight-line tree with one additional point occurrence. Extra signatures containing at least three labels satisfy the clamping theorem. [Cover classification](../seventeen-mixed/line_basis.py) · [Clamping proof and checks](../eight-line-surplus/README.md)

For a two-label extra E=T∨U, a repeated raw T, U or E is covered by the special-pair proof. An exterior raw K is handled by splitting on the placement of its two occurrences at the exceptional AND. [Special pair](../eight-line-surplus/pair-special.md) · [Repeated raw input](../ordinary-line-nine/repeated.md) · [Exterior K](../ordinary-line-nine/repeated-outside.md) · [Opposite children](../eight-line-surplus/repeated-k-split.md)

For a repeated mixed wire D, count the ordinary resident raw labels other than T and U. The special-pair proof handles at least two. There is a separate proof for zero. With exactly one ordinary resident K, the eight subsets of special source leaves entering D exhaust the remaining cases. An empty subset reduces to guarded K. The single-inside proof covers six other subsets, and the two-raw-inner proof covers the last. The marked geometry checker counts 11,340 marker extensions and 3,780 punctured double-arm extensions. [Zero residents](../eight-line-surplus/shared-no-ordinary.md) · [Single-inside proof](../eight-line-surplus/single-inside.md) · [Two raw sources](../eight-line-surplus/two-raw-inner.md) · [Geometry checker](../eight-line-surplus/verify_split.py)

## Nine line wires and a read-once mixed cone

The sample cover permits seven singleton line signatures and two genuine extras, or one of 24 banks missing a singleton. Empty and duplicate signatures reduce as above. Of the 7,140 ordinary banks, 6,118 cost at most five line gates. The remaining 1,022 cost six. All 24 missing-singleton banks are excluded by the line-tree and point-projection certificates. [Cover replay](check9.py) · [Line costs](banks.py) · [Missing-singleton proof](../missing-line-nine/README.md)

Among the 6,118 affordable ordinary banks, 3,361 have the full set of pinning witnesses. Of the 2,757 remaining banks, all placements without a raw-splitting AND are excluded by double clamping. For 531 of these banks stronger split witnesses also exclude every placement. The punctured cases divide into 531 with no missing split edge, 2,016 with one edge, 105 with two disjoint edges and 105 with two adjacent edges. Single-edge and disjoint-pair exceptional splits use the compartment checks. Adjacent-pair and triple splits use the final charge and four-private-group arguments. [Full pinning](../ordinary-line-nine/README.md) · [Double clamping](../double-clamp/no-and.md) · [Single and disjoint edges](../ordinary-line-nine/exceptional.md) · [Final single-edge cases](../ordinary-line-nine/finish-single-edge.md) · [Adjacent pair](adjacent/PAIR.md) · [Triple](adjacent/TRIPLE.md) · [Four private groups](../four-private-groups/README.md)

All six cells exceed the total budget of 33 gates. The existence of a 33-gate residual separator remains open. The replay is distributed across the linked certificates. Each covers the case stated in its note. The adjacent-pair replay uses Python-SAT with CaDiCaL, while the missing-singleton and private-group checks use Python and C++.
