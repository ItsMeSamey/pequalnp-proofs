# Distinct trace-splitting starts behind a common separator

Use actual KW pin receipt ranks r_v on each chosen star(v) square under one fixed rule. Choose an antichain T of gates meeting every forward path from each selected raw pin consumer to the output. Require every gate below T counted here to be deletable and every path from it to a permanent reader to meet T. Let R_v be the sum, over t∈T, of ranks of the actual arrival matrices at t on that same square. For nonzero r_v, R_v≥1.

For each v retain all physical path segments of actual KW runs on this square from T to its selected pin. Let B_v be the gates in those segments at which both different physical operand slots occur on some of the retained segments (possibly on different runs). Include such a gate of T if it splits. Then r_v≤R_v·2^{|B_v|}. Indeed each run reaching the pin crosses T exactly once. For fixed t, each individual segment is specified by its branch decisions at B_v: all other nodes in the union of segments have one used outgoing reverse operand. Thus there are ≤2^{|B_v|} segments per t. For a fixed segment the pairs following it are the original t-arrival matrix restricted by a row mask and a column mask from its decisions. Its rank is at most the restricted t rank. Distinct segments give pairwise disjoint receipts and rank is subadditive.

The union of B_v consists of distinct physical starts behind T, with no need to charge path multiplicities. If λ_v≥0 and Σ_{v:g∈B_v} λ_v≤1 for each physical gate, then

Σ_v λ_v log₂(max(1,r_v/R_v)) ≤ |∪_v B_v| ≤ k+Σ_{t∈T} c_t

in any gate minimum with a fixed library costing k and valid common-proof trace recipe costs c_t. The first inequality follows by summing |B_v| against the fractional weights. The second is the single simultaneous physical separator bound. The left and right sides use the same T; for a gate already counted as a raw consumer, one may take the union with consumers but may not add it twice. This lemma yields no positive lower bound from rank generated wholly above T. The affine banks warn against assuming low overlap among the B_v or invoking independent libraries.
