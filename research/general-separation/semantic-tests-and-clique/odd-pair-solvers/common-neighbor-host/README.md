# Two-pin odd supports on promised degree-five hosts

Given two distinct original pins in a simple undirected graph, the solver seeks a vertex set containing both pins in which every induced degree is odd. The host promise is maximum degree at most five, with every pair sharing three or more neighbors having both endpoint degrees at most four. The solver checks the promise. Read degree-five-common-neighbor-host.md for the deterministic polynomial reachability and first-conflict proof. Its state space carries a 128-layer window; the polynomial theorem gives no practical resource guarantee on large arbitrary instances.

## Run

Use Python 3.10 or later. The solver uses only the standard library.

    python common_neighbor_host_solver.py input.json

The same command without a filename reads standard input. A graph is indexed from zero and each edge must be listed symmetrically. For example:

    {"neighbors":[[1],[0]],"pins":[0,1]}

YES contains the verified list of original witness vertices. NO certifies absence under the checked promise. Outside the promise the solver returns UNKNOWN unless the two pins themselves form an edge.

## Replay

    sha256sum -c SHA256SUMS
    python common_neighbor_host_check.py

The checker uses NetworkX for graph generation and its graph atlas. The clean release replay used CPython 3.12.14 and NetworkX 3.7. It compares 510 small inputs to direct subset enumeration and separately exercises 172 remote-chord repairs, including two physical vertex identifications. The two off-promise review augmentations are genuinely NO by direct subset enumeration; the solver correctly returns UNKNOWN. Their original source fixtures and explanation are in review/. The review JSON uses integer adjacency masks, not the public CLI format.

The supporting width-seven proof and previous release controls are provided intact inside width-seven-odd-supports-release.zip (SHA-256 35012c0114a903e218edd9d2377139804acbb498eb2efd876cc460c8bff2af06). Extract this inner archive into a separate directory for its manifest, theorem and README. The promised solver's computational dependencies are included at the top level.
