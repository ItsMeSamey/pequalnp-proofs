# Star-forest deletion and branching in projective-plane incidence decoders

Let a one-per-shore binary monotone circuit reject each individual raw flag. This holds if every row and column of its target contains a zero. Write h for the number of distinct branching wires, including raws. The group decomposition in branching-packing.md partitions the positive edges into a union of vertex-disjoint within-group bicliques and at most 2h additional cross bicliques. The cross bicliques are edge-disjoint, indexed by the earlier endpoint's group and shore. They may share vertices.

Let the graph be C4-free with v≥1 vertices, m edges and maximum degree Δ≥1. Each biclique is a star. The within-group graph is a star forest, of size at most v−1 edges, and each cross star has at most Δ edges. Hence h≥ceil((m−v+1)/(2Δ)).

Choosing a center in each nonempty cross star yields at most 2h vertices whose deletion leaves a star forest. For a single-edge star either endpoint works. Write τ for the minimum vertex deletion to a star forest. Then h≥ceil(τ/2). On a bipartite graph τ is its four-path vertex cover number: every connected bipartite graph with no simple path of three edges is a star or isolated vertex.

Each star with a≤Δ edges has a+1 vertices, so any star forest has at most Δ/(Δ+1) edges per vertex. Deleting k vertices removes at most kΔ edges. Thus m−kΔ≤(v−k)Δ/(Δ+1), giving τ≥ceil(((Δ+1)m−Δv)/Δ²).

In any finite projective plane of order q≥2, N=q²+q+1 points and N lines each have degree q+1. Any two points lie on a unique common line, so the incidence graph is C4-free. Substitution of v=2N, m=N(q+1), Δ=q+1 gives τ≥ceil(Nq/(q+1))=q²+1. Equality holds: delete all q² points outside one chosen line, then delete only that line. Each remaining line meets the chosen line once. There remain q+1 disjoint stars each with q leaves. The elementary edge-loss estimate gives h≥ceil(q³/(2(q+1))), while the vertex deletion yields h≥ceil((q²+1)/2).

Every one of the 2N flags is essential: omitting any would accept its positive incident edge on the opposite singleton alone, making that opposite vertex universal. The live binary fanout count gives total size g≥2N−1+ceil((q²+1)/2). For the Fano plane τ=5, h≥3 and g≥16. Only the graph deletion number was shown exact.

## Related primary work

Claim 3.5 in Jukna's *On Graph Complexity* uses the same fact that a biclique of a C4-free bipartite graph is a star. It bounds the edges in a union of vertex-disjoint bicliques (a “fat matching”) and links covers by such unions to depth-three circuit models. Here the circuit partition produces one such union plus two individual cross bicliques per branching wire. [Jukna's paper](https://eccc.weizmann.ac.il/report/2004/005/download/)

Brešar, Jakovac, Katrenič, Semanišin and Taranenko study the minimum number of vertices meeting every path of a prescribed order and prove regular-graph bounds. For bipartite graphs their four-vertex path cover parameter is exactly the star-forest deletion number here. [On the vertex k-path cover](https://doi.org/10.1016/j.dam.2013.02.024)

Projective-plane incidence matrices are classical examples in the complexity of Boolean matrix–vector multiplication by multi-output OR circuits. That model computes an entire vector; the decoder here computes a single incidence bit on the one-per-shore domain. [Separating OR, SUM, and XOR Circuits](https://pmc.ncbi.nlm.nih.gov/articles/PMC5432968/)
