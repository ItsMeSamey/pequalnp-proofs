# Finding an induced all-odd subgraph through two specified vertices

The [solver release](odd-pair-solver-release.zip) returns a witness on the original vertex labels or decides infeasibility on the classes below. It includes the proofs, Python implementations, a JSON command-line interface and offline regression tests.

- When every edge belongs to at most two ordinary four-cycles, the algorithm takes O(n⁴) time in the adjacency-matrix RAM model. Four-cycles may have chords.
- On graphs of maximum degree three, twin folding and the four-cycle algorithm give a polynomial-time solver.
- On graphs of maximum degree four with k vertices of degree four, search takes 2^min(k,n/3) poly(n) time and polynomial space.

After extracting the archive, run `sha256sum -c SHA256SUMS` and `python -I -S replay.py`. The tests include cases where two visits to the same ordered pair of pins have different answers because earlier steps removed different vertices. The archive README compares the pinned problem with the classical unpinned cardinality theorem and records a separate conditional SAT baseline.

Archive SHA-256 is `33372231da51d90fb0410ccf1f777698907ee98bbd94f5456e95501fcb0940ce`.
