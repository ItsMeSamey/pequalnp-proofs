# Directed Hamiltonian-cycle counting by a signed rectangle network

Let N≥1 and m count vertices and arcs of a labelled directed multigraph. A tour is an arc subset forming one spanning directed cycle, including a loop when N=1. Set s=Θ(N+m+2). The Boolean tensor contraction theorem of the October 25 OpenAI preprint gives a deterministic exact count in poly(s)·2^{O(s/√log s)} bit operations and poly(s) space. Parallel arcs are distinguishable. Deduplicating first gives the simple-digraph convention. The reduction uses the internal tensor theorem. [Pinned theorem](https://github.com/openai/math/blob/92b516ef8e/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex#L15-L48)

Tulsyan previously gave deterministic exact counting, decision and search at this rate for sparse graphs under internal network premises of the Anthropic manuscript. Section 11 extends that result to directed graphs. Theorem 1.3 improves the dependence on growing average degree. The construction here uses a signed directed cycle-cover identity and a rectangular decomposition of inversion parity with the OpenAI theorem. [Tulsyan, Theorems 1.2–1.7 and Section 11](https://hexagonmath.org/pdf/2610.00672v1)

## Cancellation

Reject a graph with any empty incoming or outgoing incidence list. Fix a root r and one total vertex order for both endpoints. A cycle cover selects one arc out of and one into each vertex, defining a permutation π. Mark any union S of cycles avoiding r, with weight (−1)^|S| times the sign of π restricted to S. Marking a cycle of length d contributes (−1)^d(−1)^{d−1}=−1. Each of the c−1 nonroot cycles may be independently marked. Their contributions sum to zero if c>1 and to one if c=1.

## Local tensors

Give each arc a unique ID. Sort all arcs twice, by (tail vertex, ID) and by (head vertex, ID). In each stream use at most g=ceil(m^(1/3)) consecutive chunks of length at most B=ceil(m/g). Two bits between an arc's tail and head chunks encode unused, selected unmarked, or selected marked. Reject the fourth code.

In each stream scan each vertex's run of incidences. Keep a two-bit state meaning no selection yet, one unmarked selection, or one marked selection. A second selection rejects. Require exactly one selection at the last incidence. If a run straddles a chunk boundary, transmit its state to the next chunk. At most one run crosses each boundary. For each vertex transmit the mark determined at the end of its outgoing run to the chunk containing the end of its incoming run and enforce equality. Pin the root mark to zero. A valid labelling determines these bits uniquely.

Only marked arcs enter sign computations. Index each arc's tail and head chunks by a and b respectively. At each tail chunk compute the sign taking its marked tail list to order (b, ID). Multiply by (−1) raised to its number of marked arcs. For each b transmit p_ab, the parity of its marked arcs destined for b, to an extra tensor. This tensor returns

    (−1)^( Σ_{a<a', b>b'} p_ab p_a'b' ).

At each head chunk multiply by the sign taking order (a, ID) on its marked arcs to its actual head list. Each computation can use direct pairwise scans. The two local sorting stages enclose a transpose of complete bundles from order (a,b) to (b,a), preserving their common internal ID order. Each inverted pair of bundles contributes the product of their sizes to the inversion parity. Thus the three signs multiply to the sign taking the marked tail list to the marked head list. Covers have precisely one marked tail and head at each vertex of S, so this is the sign of π restricted to S.

There are 2m arc bits, N vertex-mark bits, O(g) boundary bits and at most g² bundle bits. Each chunk uses O(B+g) ports since at most B vertex runs end there. The extra tensor has degree at most g². Subdividing every wire by a degree-two equality tensor makes the network bipartite and doubles the number of wires, with a unique extension of each assignment. Maximum degree O(s^(2/3)) is at most ceil(s^(9/10)) for large s. Handle bounded sizes directly. Port listings and entry evaluation take polynomial bit time and space.

Use ell=1 and P0=m+1 in the source ring. Represent negative units modulo 2^P0. The nonnegative final count is at most 2^m, so its residue is exact. Testing positivity decides Hamiltonicity. Following a positive initial count, consider deleting each arc once, retaining a deletion if the new count is positive. An arc forced earlier remains forced when the feasible family shrinks. The remaining arcs form one spanning cycle. A degree check and root traversal verify the output. There are at most m+1 counter calls.

The [independent checker](signed_bundle_check.py) compares 21,610 signs, the contributions of 1,810 covers and all 638 graph totals to direct enumeration. Cases include all 512 three-vertex simple digraphs with loops allowed, parallel arcs, split high-degree vertices and asymmetric chunk sizes. Stream states and port bounds are proved analytically.
