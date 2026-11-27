# Distinct point feeders and their query-line reuse

Normalize an original-promise polynomial-size DAG by fractional-line-cover-pinning.md, preserving all flag and singleton tests. Let s be its size, M≥1 an upper bound on the fractional geometric line cover of each physical wire's pure-point singleton support A_g. Let L_g be its pure-line singleton support. For each line l, form a set D_l of physical wire identifiers g: include g if some AND has inputs g,h, l∈L_h minus L_g, and at least one incident p belongs to A_g minus A_h. Both orientations are permitted; collapse duplicate pairs (g,l) arising at different gates. Set T=sum_l |D_l|. Then

    (2Ms+N)·2MT ≥ (q+1)N².

For each flag start at the output, true on that pair and false on both singletons. At an OR choose a child true on the pair; it must be false on both singletons. At an AND descend to any child with this same property when available. Otherwise both children are true on the pair and each is true on at least one singleton. Since the AND is false on each singleton, the two children have exactly the opposite singleton types, giving a qualifying orientation in D_l for this p. Such a trace terminates because no raw is true on the pair and false on both singletons. Therefore the singleton supports of the actual wires in D_l cover every neighbor of l. This does not require that any AND itself reject all false pairs.

For h_l=max_g |A_g∩l|, we have h_l≥(q+1)/|D_l|. The rich-line inequality gives 2Ms+N≥(sum_l h_l)/(2M). Summing the reciprocals of |D_l| and applying Cauchy gives the displayed bound. T counts each physical point feeder only once for a given line regardless of reconvergence. For example, if every eligible line-side operand covers at most w line singletons, T≤2sw and s=Ω(N sqrt(q/w)/M) whenever sqrt(q/w)→∞. In particular for a linear-size normalized DAG, T=Ω(Nq/M²), forcing large aggregate line reuse. The tradeoff provides no universal upper bound on T.

There is also a direct raw-reader charge. Consider H line variables all of whose direct physical readers are ANDs, after redundant tied gates have been folded. For each incident p compare its singleton with the flag. The earliest changed gate reads the queried raw directly and its other operand was high on the point singleton. Thus line x has h_x≥(q+1)/d_x, where d_x is its number of raw reader slots. Since sum_x d_x≤2s, the same computation gives

    s ≥ H(√(2q+3)−1)/(4M).

This implies Ω(N√q/log q) if a constant fraction of the lines have this AND-only property after normalization, without any individual raw fanout bound.
