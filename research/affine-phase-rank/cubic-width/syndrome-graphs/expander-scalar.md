# Fixed-syndrome scalar hardness on bounded-degree expanders

Exact counting of private-AND graph CNFs is #P-hard on bounded-degree constant-edge-expanders with every syndrome fixed to one. The reduction uses one exact query and polynomial bit arithmetic. Every queried CNF is satisfiable.

Begin with #perfect-matching on a 3-regular bipartite H (Dagum–Luby, Approximating the permanent of graphs with large factors). Pad with forced disjoint pairs to put each shore size at the next square. Add a bounded-degree expander scaffold on the left shore alone; the Margulis–Gabber–Galil square-order family suffices, deleting loops and merging repeats at a constant loss in expansion. The resulting graph G has precisely the same perfect matchings because matching every right vertex consumes all left vertices. Fix any perfect matching (polynomial to find or independently return zero). For a cut in G, each split matched pair gives one boundary edge. The expanding left scaffold gives at least h times the smaller population of left representatives. The smaller full shore size is at most twice this smaller left population plus the number of split pairs. Thus G has fixed positive expansion. Write n for its even order and E for its edge count.

On a graph J with N vertices, native variables t_e=x_e y_e give three preimages for t_e=0, one for t_e=1. Vertex incidence checks ∂t=b have deterministic bounded-width, bounded-occurrence CNF encodings at fixed degree. The exact count Z satisfies
    2^N Z(J,b)=Σ_s (−1)^{s·b} ∏_{uv} W(s_u,s_v), W(equal)=4, W(diff)=2.
The sign convention here uses native preweights 3^{|E(J)|−|t|}.

Choose an admissible square k≥n+2, k=O(n). Replace each base vertex by k clones with a fixed-degree expander on these positions. Subdivide each internal edge once with a fresh midpoint. For each base edge connect the two clouds via a full matching of the k corresponding clones. Put native syndrome one at every physical vertex. Every internal midpoint contributes
    Σ_z (−1)^z W(s,z)W(z,t) = 12 (−1)^s 1[s=t].
Thus each cloud has one common spin. In a cloud with q_v internal edges, k clones and the q_v midpoints contribute sign (−1)^{(k+q_v)s}. If k+q_v is even, add a single pendant leaf, also of syndrome one; summing it yields 2(−1)^s. This produces the desired effective sign (−1)^s per base vertex. Write q for the total number of internal cloud edges and t for the leaf count. Then N=kn+q+t is even since k+q_v+leaf_v is odd in each cloud and n is even. The queried all-one syndrome is feasible by spanning tree elimination on a connected even graph.

For expansion before subdivision let R be the sum of the minority clone counts in each cloud. If L is the size of a cut with smaller side s, cloud expansion gives L≥h_C R. Rounding each cloud to its majority gives L≥h_B s−(h_B+D)R using base expansion h_B, base maximum degree D and the full external matchings. Hence L/s≥h_B h_C/(h_C+h_B+D). Subdivisions and leaves preserve a fixed expansion constant: assign each new vertex an adjacent old owner; all owners have constant load. The old shore boundary uses edge-disjoint new paths witnessing crossings. Each new vertex discordant with its owner also supplies a distinct crossing, so the new smaller shore size is at most a constant times the old smaller shore size plus the new boundary. Degrees remain bounded.

Set C_j=Σ_{s:cut_G(s)=j}(−1)^{Σ s_v}. One native all-one-syndrome count gives
    2^N Z(J,1)/(12^q 2^t 2^{kE})=Σ_{j=0}^E C_j (2^k)^{E−j}.
Centered radix digits recover every signed C_j since |C_j|≤2^n<2^{k−1}. Character orthogonality yields
    Σ_{∂U=1} z^{|U|}=2^{-n}Σ_j C_j(1+z)^{E−j}(1−z)^j.
The coefficient at n/2 counts perfect matchings exactly, because every vertex has odd degree and their sum is n. It is #PM(H). Graph and CNF size and the relevant integer bit lengths are O(n²), apart from ordinary encoding overhead. All decoding and binomial arithmetic needs polynomial bit time. This hardness concerns the complete exact scalar; SAT decision on the constructed instances has the constant answer YES.
