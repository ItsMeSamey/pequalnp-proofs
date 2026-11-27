# Width-seven minimal odd supports

Every inclusion-minimal induced all-odd support through two distinct named vertices has pathwidth at most seven when its induced maximum degree is at most five. See [the constructive proof](degree-five-leaf-cap-pathwidth.md) and the [unmarked-leaf descent supplement](disjoint-pin-descent-unmarked-leaf.md).

## Two program entry points

Both commands accept a JSON file or standard input. Vertices are numbered from zero. Every neighbor list must describe a simple undirected graph, with each edge present in both directions.

    {"neighbors":[[1],[0]],"pins":[0,1]}

* `python high_pin_odd_pair.py input.json` searches an arbitrary host for a minimal support with induced maximum degree five and both pins of induced degree at least three. A positive result gives original vertex indices. Adjacent pins give their own witness with `high_pin_minimal=false`. A negative class result gives `unrestricted="UNKNOWN"`. Search takes O(n⁶ log n) on arbitrary hosts and linear time for fixed host degree, including indexing.
* `python odd_support_path_decomposition.py input.json` takes the selected support itself. Supply a graph of odd degrees at most five. For a minimal input the construction returns bags of width at most seven on the original indices. Every `CERTIFIED` output is checked for vertex coverage, edge coverage, interval continuity and width. Minimality is a completeness promise. On other admissible inputs the algorithm may return certified bags or `UNKNOWN`.

For the example above the finder returns the edge and the constructor returns the single bag [0,1]. Neither entry point needs third-party packages.

## Verification

Use Python 3.10 or later. The release replay used CPython 3.12.14 and NetworkX 3.7. Install NetworkX to run the complete controls. From the extracted directory, check integrity with `sha256sum -c SHA256SUMS`, then run:

    python single_leaf_high_pin_check.py
    python single_leaf_high_pin_shells.py
    python single_leaf_raw_terminal_replay.py
    python leaf_cap_support_check.py
    python exceptional_seven_pin_shells.py
    python exceptional_terminal_replay.py
    python high_pin_odd_pair_check.py
    python odd_support_path_decomposition_check.py

The order-eight atlas test enumerates small graphs directly. In the one-leaf census the producer and terminal replay share initial cores and nonterminal transitions and generate terminal completions separately. The exceptional replay independently generates roots up to root-neighborhood permutations and enumerates terminal completions, with the nonterminal transition shared. Counts of physical histories retain their labeling conventions. The host-finder controls compare against exhaustive original subsets. The decomposition controls check bag axioms independently on prime diamond chains through 516 sites and both inverse caps for every retained exceptional representative.

The bundled base is the biconnected release, SHA-256 `a5838d171321bf3eded55ea0d55ac614f9825401de62245a617ee341aaa031f8`, published at [commit f00719b](https://github.com/ItsMeSamey/pequalnp-proofs/commit/f00719bb640a65b5156dc1fa1c002c0135713e66). No DOI has been assigned. Its [original README](README-biconnected.md) lists the earlier replay commands. All its payload files are preserved, with that README renamed and the release-wide checksums regenerated.
