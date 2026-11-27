# Path packing forced by minimum size for every fixed semantic library

Use semantic-bank-mincut.md with n deletable gates, a fixed shared library costing k, and fixed tap recipe costs c_v (unavailable recipes have infinite capacity). In a minimum circuit, at least n−k distinct deletable gates can each start a path following original physical reader edges to a permanent reader or output sink. Counting an initial gate as traversed, no finite-recipe gate v is traversed by more than c_v paths. For n≤k the assertion is vacuous.

All cuts in the semantic deletion network cost at least n−k by minimum size. Integral max-flow supplies that many paths. The unit-capacity source arcs force distinct starting gates. Each visit to v crosses v→z_v before traversing an original reader edge; its capacity is c_v. Conversely such paths certify the absence of strict saving for this fixed cost ledger.

If T consists of finite-recipe gates and every path from each old deletable gate in P to a permanent reader intersects T (starts in T count), then |P|≤k+Σ_{v∈T}c_v. At most k starts are omitted; every remaining P-start uses capacity at some T site. One packing witnesses all separators simultaneously. The conclusion requires no fanout or depth restriction. A plane lower bound still requires finding many physical starts behind a cheap recipe separator.
