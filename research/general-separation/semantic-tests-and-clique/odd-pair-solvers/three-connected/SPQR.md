# Why the reduced SPQR tree is a path

Let H be a finite simple biconnected induced all-odd subgraph containing two prescribed vertices. Assume no proper subset of H containing both pins induces all odd degrees, and every vertex of H has degree at most five. Then its reduced SPQR tree, with real edges retained in the skeletons and without Q leaves, is a path. Every leaf of a nontrivial tree must contain a pin in its exclusive interior. Distinct leaves have disjoint interiors, so there are at most two. [Proof](universal-pair-shore-spqr-path.md)

The proof analyzes a pin-free part attached through two boundary vertices. It records the four choices of which boundary vertices are selected and the four incoming parity pairs. If all sixteen combinations work, a binary matrix argument constructs a smaller witness that still contains both original pins. The finite leaf classification supplies precisely this obstruction. The mixed boundary-parity case has orders seven and eleven, giving twelve and forty-eight labeled presentations. Together with the four six-site presentations, all 64 pass the table test with either value of the real boundary edge. [Mixed classification](mixed-rooted-three-connected-limb.md) · [Two-boundary composition](odd-block-path-and-edge-limb.md) · [Independent audit](audit/spqr/audit.md)

Internal skeletons may have two virtual edges; their size remains open. For supports with articulations a separate result bounds the number of leaves per block. That result does not classify the full support. [Per-block bound](multiple-free-shores-spqr-leaves.md)

From this directory, run the following to check the frozen sources, regenerate the two terminal censuses and compare the physical boundary tables. The two terminal implementations share a previously checked generator for nonterminal prefixes. The final independent check enumerates 4,871 small exterior configurations and pin placements directly.

```sh
sha256sum -c SPQR-SHA256SUMS
python mixed_torso_full_census.py
python mixed_edge_torso_raw_terminals.py
python all_pendant_torso_tables.py
python audit/spqr/check.py
```

For the additional 555 witness-lifting controls, run `python universal_limb_escape.py` with NetworkX available.
