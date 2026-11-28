# Rank-cover separation on connected cycles

In the literal model with empty binary background B, every strict three-literal violation has a unique degree-three monomial, with coefficient one, on its scope. A pivot resolves exactly the clauses containing it, simultaneously for all sign patterns on any one scope. For a missed scope its cubic coefficient is zero in the entire selected span. Thus on unpinned entirely strict 3-CNF, connectivity and the decision outcome do not change equality of rank-cover and ordinary pivot-cover optima.

With a genuine binary background, the following connected examples have strictly ternary residuals. Take m≥3, indices modulo m, and one hub w. The background consists only of (¬a_i∨¬b_i). The target rows are (a_i∨b_i∨c_i). For each binary expression (a_i∨c_i) and (¬b_i∨c_i), introduce both ternaries obtained by adding w or ¬w. Similarly for every edge of the c-cycle encode (c_i∨c_{i+1}) and (¬c_i∨¬c_{i+1}) with both guard polarities. All ternaries contain three distinct identifiers.

Let v denote the GF(2) violation indicator on B-models. For each i, a_i b_i=0, so the target's indicator equals

    (1+a_i)(1+b_i)(1+c_i) = (1+a_i)(1+c_i) + b_i(1+c_i).

Each term on the right is a binary violation, equal to the sum of the indicators of its two complementary guarded rows. All guarded rows resolve on w. Thus w certifies the complete row span. The rank-cover optimum is exactly one: each target has nonzero violation and all three singleton truth patterns extend B; the guarded witness rows likewise admit all three singleton patterns. No row is unconditionally reducible.

For ordinary pivot cover each target requires one of its three names. Any outside pivot has at least one feasible pin under which every singleton on this target still extends B, since the background consists of disjoint binary bans on a_i,b_i. The ordinary optimum is exactly m, attained by selecting every c_i. The raw incidence graph is connected.

The represented system is satisfiable exactly when m is even. A two-colouring of the c-cycle extends by setting every a_i=1 and b_i=0, with arbitrary w. Conversely the four guarded rows per edge enforce disequality for either w. Any subset omitting all clauses for one edge is satisfiable by colouring the path, hence every unsatisfiable subset uses at least m distinct edge groups. These are parameter comparisons, and direct recognition of the cycle also decides these controls.
