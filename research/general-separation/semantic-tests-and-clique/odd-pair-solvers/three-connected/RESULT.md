# Six- and eight-vertex minimal pinned odd supports

Every 3-connected, inclusion-minimal induced all-odd support through two specified vertices with induced maximum degree at most five has six or eight vertices. Up to isomorphism preserving the unordered pins, there are two six-vertex types and nine eight-vertex types. All selected vertices lie in the union of the two closed pin neighborhoods. [Proof and classification](degree-five-three-connected-shells.md)

The [finder](three_connected_odd_pair.py) uses the original graph and returns original vertex labels. A negative answer decides the structural query. It returns UNKNOWN for unrestricted existence because a witness of lower connectivity or higher degree may still exist. [Direct oracle](three_connected_odd_pair_check.py) · [Independent completeness audit](audit/completeness.md)

The oracle checked all 32,768 labeled six-vertex graphs with fixed pins, plus 200 relabeled exterior extensions. Both terminal implementations use the same generator for nonterminal prefixes. A separate implementation checked those transitions. The [replay instructions](README.md) cover all ten checks using Python's standard library. The supplementary archive has SHA-256 `7ab12239d1f5e0f5cd2a1c6bdca11e905270fe577ccd1f31982b51718522f37e`.

## Extension to biconnected supports

The same six/eight classification and finder cover every biconnected minimal support of order at least three and induced maximum degree at most five. If its reduced SPQR path had two ends, each end's pin would have a private neighbor. The two disjoint pin-neighbor edges would induce a proper all-odd subgraph, contradicting minimality. The support must therefore be one of the previously classified three-connected types. Failure of the finder still leaves unrestricted existence open. [Biconnected proof](biconnected-odd-six-eight.md) · [Full release with census and checks](biconnected-minimal-odd-supports-release.zip)
