# Full-promise endpoint signature counts

In any finite projective plane of order q≥2 take the exact OR of all distinct products p∧l for flags (p,l). A native flag selects its unique true product. On an independent negative with query set L, |L|≤q, put d(p)=|L∩star(p)|. For 1≤k≤q the physical AND at (p,l) returns p iff l∈L or d(p)≥k, and returns l otherwise. The first case has a queried neighbor so p is absent, the second has l absent. The gate-local decision only uses the negative mask and the fixed identity of its gate.

For a site v record the subset of flags in its star on which the point endpoint is returned. At p this is its full star or exactly its queried substar of size <k. Every such subset occurs by querying just that subset, and k neighbors yield the full set. Each point has precisely 1+Σ_{j=0}^{k−1} binom(q+1,j) signatures.

A queried line receives the full point-return set. At unqueried l the returned points have d(p)≥k and Σ_{p∈l} d(p)=|L|≤q. Every subset of ≤floor(q/k) points of l occurs: query k lines other than l through each chosen point. Pencils of distinct chosen points share only l. Thus each line has precisely 1+Σ_{j=0}^{floor(q/k)} binom(q+1,j) signatures.

The rule ignores the payload, so the counts are identical on all independent masks and on all same-query maximal negatives. At k=ceil(sqrt(q)) every log-support size is O(sqrt(q) log(q+1)), sublinear in q. The largest shore log-support is Θ(sqrt(q) log q) after optimizing over this threshold family: max(k−1,floor(q/k))≥floor(sqrt(q))−1, and the matching lower bound follows from the binomial coefficient at that size.

This refutes a q-bit mandatory per-site endpoint-signature claim even with all legal negatives and real local tie decisions. The formula has 2N(q+1)−1 gates. It supplies no small-total circuit, no minimum claim, and no upper bound on internal trace signatures of all circuits.
