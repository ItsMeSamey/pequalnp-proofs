# Every small set of raw sites has a simultaneous receiver budget

In the bilateral normalized order-401 circuit, take any set X of at most 399 points and at most 399 lines. Let R(X) count physical fanout units above two at its raws. Let A(X) count distinct nonprivate AND gates with a raw operand in X whose other operand remains nonzero after zeroing X. A witness of any size on surviving raws suffices. Then

    s ≥ 4N−4 + R(X) + A(X),  N=161203.

Pick a point pole outside the X points and the union of the X lines: at least N−399−402·399=406 choices. Pick a line pole outside the X lines and avoiding every X point and the point pole: at least N−399−402·400=4 choices. Their full dominating theta is disjoint from X. After deleting X all vertices still have at least 402−399=3 neighbors. First-stage zero flow charges the raw excess and nonprivate exactly-one-zero ANDs in separate physical terms. Refresh the restricted-variable normalization before deleting remaining noncore sites, each of which has a permanent theta neighbor. The residual costs 4(q+1), giving the inequality by the two-stage theorem of planted-theta-credit.md.

Every below-target normalized circuit must therefore have R(X)+A(X) at most 1616 for every such X. Credits from different choices are not summed. For instance 810 distinct nonprivate readers x AND H of one raw x, all with H surviving x=0, give at least 808 raw-excess units and 810 separate AND credits. No singleton witness on H is required.
