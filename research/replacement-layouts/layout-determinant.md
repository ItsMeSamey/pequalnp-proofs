# A rank obstruction for arbitrary replacement layouts

Use the partitions, per-factor assigned groups, groupwise measurement matrices and polynomial rows in the definition labeled def:layout of OpenAI's October 2026 ETH manuscript. The following argument works over any field admitting the Q distinct nonzero evaluation points. It needs P_{f,v}(0)=e_v, row degree ≤R and off-group rows in the span of that group's measurements. Put c_t equal to the sum of the ranks of the group matrices at point t.

Choose one incident factor f_v for each included variable v; omit variables without a choice. Let a_v(t) be its variable group and d_v(t) the group assigned to f_v. Write h_v for the number of mismatches between these two group words. Then

    sum_t c_t ≥ sum_v E[max(Bin(2h_v, 1/2) − h_v − R, 0)].

Here the positive part is taken inside the expectation.

Proof. Color each (point,group) independently by a fair bit. Write Z_v for the sum over points of target-color bit minus source-color bit. Let V consist of the variables with Z_v>R. Form the square polynomial matrix B on V using the chosen row of each variable and restricting to the columns V. B(0)=I so its determinant is nonzero and has degree at most R|V|. At t, B(t) decomposes into a local matrix (each row supported on its target group) plus a matrix of rank at most c_t, because each off-group restriction is in the measurement row space. The local matrix has nullity at least the number of rows with target bit one minus the number of columns with source bit one: the specified rows are all supported on these columns. Subtracting c_t gives a lower bound on nullity of B(t), valid also when negative. If B(t) has nullity j then an invertible constant row transformation renders j rows zero at t. Each then has polynomial entries divisible by (T−t), so det B vanishes to order at least j. Summing over distinct t gives total nullity at most R|V|. Rearrangement yields sum_t c_t ≥ sum_{v in V}(Z_v−R). Each Z_v has the law of Bin(2h_v,1/2)−h_v, because a mismatched point contributes two independent fair bits with opposite sign. The Z_v need not be independent. Linearity of expectation proves the inequality. The empty V case is immediate.

**Worst-case scopes.** Take a family of constant-degree n-vertex edge expanders of maximum degree Δ and expansion η>0 on vertex sets of size ≤n/2. Use a binary factor on each edge. If r≥4 then every variable group has size ≤n/2. Summing edge boundaries over groups, at least ηn/2 edges cross groups at every point. At each crossing edge at least one endpoint's source group differs from the factor's target. Sum over points, then for each v choose the incident edge maximizing its mismatch count. This gives sum_v h_v ≥ ηnQ/(2Δ). Writing γ=η/(2Δ), at least γn/2 variables have h_v≥γQ/2 (a weaker bound suffices). This selects one fixed factor per variable before choosing random color bits. The lexicographically constructed graphs in the [balanced-cut construction](../violation-certificates/barrier.md) may substitute for expanders: group whole color classes into shores of size at least n/3, and use their linear induced matching to obtain the same linear crossing-edge count for a different absolute γ.

**Tail estimate.** For Y=Bin(2h,1/2)−h and 0≤R≤h/4, one has E[(Y−R)_+]≥c√h exp(−C R²/h) for absolute c,C and sufficiently large h. Stirling's bounds give Pr[Y=0]≥c'/√h. The exact ratio Pr[Y=j]/Pr[Y=0]=prod_{i=1}^j (h−i+1)/(h+i) bounds each centered atom below by (c'/√h)exp(−C' j²/h) for 0≤j≤h/2 (increase constants for small j). Sum over the order-√h integer values from R+√h to R+2√h, each contributing an excess of at least √h. Taking R≤γQ/8 and using Q≥h≥γQ/2 for the selected positive fraction proves, for large Q,

    2τnQ ≥ sum_t c_t ≥ c₁ n√Q exp(−c₂ R²/Q).

Constants depend only on η,Δ. Equivalently τ≥c Q^(−1/2)exp(−C R²/Q). This constrains replacement layouts, not the computation time of arbitrary SAT algorithms. A general catalogue-size lower bound exponential in Q log r does not follow.

These inequalities apply to the direct replacement layout specified above. The precision-weighted construction in Appendix D has a different accounting argument. [Manuscript source](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex)

[Lean determinant-nullity budget](../../lean/Research/DeterminantBudget.lean). [A complementary group-support budget](layout-group-budget.md) also follows from the diagonal replacement polynomials.
