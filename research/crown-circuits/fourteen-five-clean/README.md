# Fourteen-input threshold two with at most five singleton-clean AND gates

A binary monotone AND/OR circuit computing threshold two on fourteen inputs cannot have at most 34 gates and at most five AND gates if every AND rejects every singleton. Equivalently, a circuit of that size and AND count must have an AND that accepts some singleton. The size of circuits with singleton-active ANDs remains open here.

The general physical conclusion uses the thirteen-input lower bound of 32 gates via [raw normalization](normalization.md). For a live circuit in which every raw has two physical reads, the [signed-bank construction](circuit-bridge.md) is independent of the thirteen-input result. It gives fourteen disjoint faces of the five-cube built from ten signed literals with at most seven proper intermediate unions. A face of width k fixes k coordinates and has 2^(5−k) atoms.

1. [One higher-width helper](one-high-helper.md) and [two higher-width helpers](two-high-helpers.md) establish the volume and edge counts, including the twin configurations.
2. [At least three triple helpers](at-least-three-triples.md) allows arbitrary quartets and excludes at most two triples under the full-receiver premise.
3. [Remaining profiles](remaining-banks.md) establishes the full-receiver premise, lower-bounds the pair helpers and leaves (4,3,0) and (3,3,1), ordered by pairs, triples and quartets.
4. [The three-pair case](three-pairs-one-quartet.md) and [the four-pair case](four-pairs-three-triples.md) exclude the remaining profiles.

For the Mantel inequality, take a vertex of maximum degree Δ in a triangle-free graph on p vertices. Its Δ neighbors are independent. Summing degrees on the remaining p−Δ vertices counts every edge, and counts edges internal to that set twice. The edge count is at most Δ(p−Δ)≤floor(p²/4). Equality forces no internal edges and full degree Δ on the remaining side, giving a balanced complete bipartite graph. This supplies the equality cases used at p=4,5,7.

The thirteen-input prerequisite is the lower-bound direction in the companion packet *Thirteen-input threshold and crown*, member thirteen-exact-assembly/RESULT.md. Its SHA256SUMS digest is c8f06a02b7b26348502dec08cd22a516bd829ae105c9150b09165843daeb9a1a. The fourteen-input proof uses no numerical solver. From this directory run `sha256sum -c SHA256SUMS` to check the frozen source hashes.
