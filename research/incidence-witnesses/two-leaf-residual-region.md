# A physical ledger for two-leaf flags and regional obligations outside their envelope

Let H be the subset of native flags with a two-leaf accepting parse in a physical circuit. If H is nonempty, take the trimmed minimum-formal-degree envelope from the rank-clean extraction: retain both inputs at products, at a sum retain children attaining its minimum formal degree, bypass unary nodes, and trace from the output. Let A be the old gate IDs retained as actual binary gates of the envelope. It computes the formal degree-two monomials, all simple graph edges by the singleton tests. The C4-free star bound gives |A|≥|H|+τ(H)−1. For H empty take A empty and use zero for this baseline.

For each line l put h_l=|H∩star(l)| and force points of those h_l flags off, and only line l on. Use the dense negative of all points off l; it is legal. The remaining q+1−h_l point singletons belonging to l are accepted. The same cold-OR trace as in regional-cold-or-packing.md yields a set C_l of distinct OLD physical OR gates, |C_l|≥max(0,q−h_l) (take no trace if no remaining points). Let a_l=|C_l∩A|. Weights w_l≥0 with Σ_{l:g∈C_l}w_l≤1 imposed ONLY at g outside A give

s ≥ |A| + Σ_l w_l max(0,q−h_l−a_l).

Indeed every contribution after subtracting overlaps uses only gates outside A, with the one-per-gate weights. One can replace |A| by its two-leaf lower bound. All projections refer to original Boolean gates under real assignments; keeping the same ID in the degree-two envelope need not preserve its signal value in the old circuit. At lines with no uncovered obligation choose weight zero.

This covers the private star formula where H is every flag: the regional test alone misses its private query producers, while the envelope accounts for the cost. To imply the official bound on arbitrary circuits, the new term must cover the remaining deficit using actual original gates; no universal bound on a_l or shared exterior marks is asserted.
