# Perfect matching and residue controls for strict cubic flows

A cubic graph has a nowhere-zero two-bit flow exactly when it has a perfect matching whose complementary two-factor consists of even cycles. Color the matching with one nonzero color and alternate the other two on every complementary cycle. A proper matching chosen without that condition need not admit this final step. Cubic three-edge-colorability is NP-complete. [Holyer](https://doi.org/10.1137/0210055)

**Exact sampling family.** For each k≥1 take 2k triangular prisms, alternating two kinds of two-terminal block. Delete a spoke in the first kind S and a horizontal edge in the second kind H. Connect the two exposed terminals of every block to its two neighboring blocks in cyclic order by single edges. This gives a simple connected bridgeless cubic graph on 12k vertices. In particular the two interblock edges at k=1 have distinct endpoints. Every block is itself bridgeless after deletion of one edge, since the triangular prism is three-edge-connected. The ring gives alternate routes around the connectors.

A prism has four perfect matchings. The three spokes leave two triangles. Each of the three other choices consists of one spoke and a horizontal edge in each triangle and leaves a six-cycle. A perfect matching on the ring uses both connectors of a given block or neither, because a block has even order. Its common choice b propagates around the ring. Identify each local choice with the closed-prism matching using the deleted edge when b=1 and avoiding it when b=0.

| Block | b=1 total / extendible | b=0 total / extendible |
|---|---:|---:|
| S | 2 / 1 | 2 / 2 |
| H | 1 / 1 | 3 / 2 |

For b=1 all complementary cycles stay inside individual blocks. For b=0 any bad block contains an intact odd triangle, while each good block contributes an odd-length path from a broken even cycle. Joining these paths by the connectors produces an even cycle because each path together with its next connector contributes even length. The ring therefore has exactly 2^k+6^k perfect matchings, of which 1+4^k are extendible to a proper three-edge-coloring. The success probability of uniform perfect-matching sampling decreases exponentially in k on these colorable inputs.

There is also an explicit lexicographic delay with 0 preceding 1. First order one connector, then all retained horizontal edges of a designated H block, then the other edges. Setting that prefix to zero forces b=0 and the all-spokes matching in the designated H. There are 2^k·3^{k−1} bad completions of that prefix, preceding every good matching. This is an obstruction for that ordering and for uniform sampling. It gives no bound for a graph-aware matching selection rule.

Run `python check-prisms.py` to enumerate entire graph matchings and test each complementary cycle. For k=1,2,3,4 the total/extendible counts are 8/5, 40/17, 224/65 and 1,312/257. The checker also tests connectedness after every single-edge deletion. An independent enumeration obtained the same counts.

[Fixed-residue and graph-cover controls](residues.md) separately classify limits of bounded modular counts, certain dense two-adic probes, and summaries invariant under graph covers. They do not apply to unrestricted support queries or to arbitrary decision-only reductions. The aggregate selector's actual regular-host witness algorithm is described in the [regular aggregate theorem](../regular-aggregate-selector/README.md).

The separate `python check-covers.py` enumerates all ordered edge colorings of the odd prisms on 6, 10 and 14 vertices (6, 30 and 126 colorings). It also counts 0 on Petersen, 192 on its bipartite double cover and 0 on its connected one-edge-twisted double cover.
