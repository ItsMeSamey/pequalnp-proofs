# Mixed boundary degrees on a three-connected limb

In a simple 3-connected graph J of maximum degree five, require the two adjacent sites a,b selected. Site a requires even degree; every other selected site requires odd degree. If the full word works and no proper word works, the order is seven or eleven. Both orders occur.

Site a has four neighbors. An exclusive neighbor c of a yields the proper word {a,b,c}. Thus there are three common neighbors C, and b has one more neighbor d since its degree is odd. The root on a,b,C,d has six free edges among C∪{d}. It cannot be the whole graph since five vertices would be odd. At least three of C∪{d} must have further capacity by 3-connectivity. Rejecting a pinned word wholly within the root leaves 60 root graphs.

In the [physical shell recurrence](degree-five-three-connected-shells.md), a diagonal one at the compulsory site a encodes even physical parity for its row. It is never counted for edge degrees or connectivity and a is not a port. Thus the proof of each nonterminal pruning test carries over. In final layers the full old word occurs only with every port selected and at incoming parities one plus the current port degrees modulo two. In that cell a second word is proper, and every word with any other occupancies or incoming parities is proper. This distinction protects full completions on one or two new sites.

| Appended nonterminal layers | Tables with degrees | Physical histories | Terminal presentations |
|---:|---:|---:|---|
| 0 | 50 | 60 | 12 of order 7 |
| 1 | 1,128 | 4,524 | 48 of order 11 |
| 2 | 32 | 372 | 0 |
| 3 | 30 | 720 | 0 |
| 4 | 14 | 384 | 0 |
| 5 | 0 | 0 | 0 |

The [physical sweep](mixed_torso_full_census.py) shares transitions at equal tables but glues all shapes to all corresponding histories. It checks original unlooped degrees, proper-word exclusion and actual 3-connectivity. The [second terminal sweep](mixed_edge_torso_raw_terminals.py) tracks raw prefix words and uses a separate terminal generator. Counts refer to presentations with C,d labeled and neighbor types sorted. One eleven-site example has adjacency masks (30,61,779,7,515,962,800,1312,1252,1140,896), a=0 and b=1.

For an actual biconnected minimal all-odd support H of maximum degree five, a pin-free shore W must have only the contacts a,b, a nonempty opposite shore, and J=H[W∪{a,b}]+ab must be 3-connected. J must realize its full-word boundary parities uniquely: any alternative would thin H while restoring the same parity at both selected sites. Mixed parity forces ab virtual, since b already has degree five in J and also meets the exterior in H. Physical shore degrees are then three and four, so a meets exactly two exterior neighbors and b meets exactly one. Local sharpness does not establish global realizability of an eleven-site limb. A torso with several virtual edges is outside these hypotheses.
