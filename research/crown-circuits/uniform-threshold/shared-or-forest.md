# Probe forests force a dense shared clique

Use the notation of shared-or-stability.md and assume K=O(h). Then d=O(√h), a=O(1), and Σ J_U≤K+h. Fix a probe U with k strict successors. At most J_U of its active ANDs are private, because each contributes a negative unit in the exact flow balance. At most a others are shared. Their total fanout is at most J_U+a+d, allowing for all AND surplus.

Choose one active incoming pin for each active OR except U. Removing the active ANDs leaves OR paths rooted at U or an active AND's output pins. Suppress private OR vertices, which have at most one outgoing pin. The k+1 active shared groups form a forest with at most 1+J_U+a+d roots, every forest edge an OR-only path and therefore a probe comparison. Every vertex W has at most f_W children. Cut child arcs above two at every vertex, at most d cuts in all. The resulting binary forest has r≤1+J_U+a+2d roots.

There are at most k ancestor pairs whose ancestor is U. Each other vertex W has at most t_W≤J_U+J_W+a descendants, by the comparable-probe loss. Thus total ancestor pairs are at most k(1+J_U+a)+K+h. In a binary forest of N=k+1 vertices and r roots, fewer than r·2^i vertices have depth below i. Sum N−r·2^i up to i=floor(log₂(N/r)) to obtain at least N(log₂(N/r)−3) ancestor pairs.

All but O(h/log h) probes have J_U≤0.1log₂ h. On these probes r=O(√h). If k≥h/log₂ h, then log₂((k+1)/r)≥0.4log₂ h eventually. Comparison gives k=O(h/log h). The omitted probes have k<h, so there are O(h²/log h) comparable pairs overall. The number of missing shared raw edges exceeds this by only q=O(h).

The shared graph is within O(h) edits of disjoint cliques. In this approximation, if m is the largest clique size, there are at least h(h−m)/2 missing cross pairs. Therefore h−O(h/log h) shared vertices span a clique with at most O(h) edges missing in the original graph. These conclusions concern regular globally minimum circuits at constant offset. They do not themselves improve the size bound.
