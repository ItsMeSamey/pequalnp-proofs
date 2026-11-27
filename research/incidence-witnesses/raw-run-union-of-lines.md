# Unions of query stars force large physical first-run induced matchings

Use the original first homogeneous AND/OR endpoint relations on point raws from raw-run-induced-matching.md, with induced matching dimensions d_A and d_O. For an OR gate v let S_v be its syntactic raw point neighborhood by OR-only paths. To allow parent slots that are not OR outputs, assign an OR input slot the upstream set {p} for a direct point raw p, the upstream S_w for an OR parent w, and the empty set otherwise. S_v is the union of these two upstream sets. No semantic estimate, normalization, or gate fanout bound is assumed.

Let Y be a fixed query set of at most q lines, U its point union. Set all points outside U high, and initially all points inside U low. The output rejects this independent mask with queries Y. Changing just p∈U to high creates a flag. On a changing path from p the first homogeneous run has a changing endpoint. For an AND run that endpoint has no raw point of U other than p in its pure AND neighborhood, as any such other low raw would force it off. There can be at most d_A distinct points of U with a witnessing AND endpoint, since separately picking a witness for each such point gives an induced matching. For an OR run its changed endpoint must contain p in its OR neighborhood and have that neighborhood contained in U, or it would already be forced on by some high point raw. The argument also works if only one query may be on: for each p use any one line of Y incident to p, keeping the same point assignment. The AND and OR neighborhood constraints are independent of this choice.

Let D be the set of raw points that have a physical OR endpoint with singleton OR neighborhood. These raw points have private endpoints globally, so |D|≤d_O. Each p∈U outside the AND exceptions and D has an OR endpoint e whose neighborhood contains p and another raw point, and lies entirely in U. Follow a pure OR path from p to e; charge the input slot of the first OR v along that path with |S_v|≥2. The charged slot has upstream set exactly {p}, irrespective of Y. For each candidate slot preselect any other point y in S_v. If the slot is charged then both its fixed p and its fixed y lie in U. Each slot is charged at most once for this Y. This remains true when many chosen paths reconverge.

For a uniform t-subset of lines (1≤t≤q), let π₁ be the inclusion probability of a fixed point in U and π₂ the joint inclusion probability of two fixed distinct points. Writing k=q+1 and Z=binom(N,t), these are
    π₁=1−binom(N−k,t)/Z,
    π₂=1−2binom(N−k,t)/Z+binom(N−2k+1,t)/Z.
These formulas use only point and pair incidence degrees, without automorphism assumptions. Counting points for each realized Y first, then averaging, proves
    d_A ≥ (N−d_O)π₁ − 2s_OR π₂,
where s_OR counts actual physical OR gates. The dimension counts and gate count concern the same original DAG.

For t=floor(−q log(1−a)) with a fixed in (0,1−1/e), one has π₁=a+o(1), π₂=a²+o(1). To check, expand the log of the hypergeometric miss probability for forbidden sizes k and 2k−1 as −t·(forbidden size)/N+O(1/q). Fix s≤CN and d_O≤(1−δ)N for some fixed 0<δ≤1. Choosing a=δ/[4(C+1)] gives
    d_A/N ≥ δ²/[8(C+1)]−o(1).
In particular in linear-size circuits d_A=o(N) forces d_O=(1−o(1))N. Thus one of the two physical first-run relations always has induced matching dimension Ω_C(N) when s≤CN. The inequality alone does not establish a superlinear gate count.
