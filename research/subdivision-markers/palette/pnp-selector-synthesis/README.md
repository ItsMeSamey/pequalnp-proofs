# Physical selectors with bounded Boolean degree

In split binary coordinates each indexed column is (private key, two-bit tag, two-bit height). Supply private coordinates compressed to the span of the keys. A chart is a linear map from private keys to tags. Indexed columns whose tags agree with the chart are active.

recognize(columns, dimension, degree) computes a basis of the constant private outputs attainable by XORs of active sites selected by Boolean polynomials of the specified degree. Each returned anchor includes a combination that selected_sites can evaluate at any chart. The coordinates of the chart are fixed before heights or witnesses are chosen.

For each nonzero key replace one input coordinate in each tag bit's linear form by that form. This is an invertible change of coordinates. A Boolean polynomial supported on the matching slice factors uniquely into the two matching literals times a polynomial on the remaining coordinates. Its degree is exactly two plus the free degree when the polynomial is nonzero. Multiplying out these generators in the original global coordinates, reducing squares and eliminating all nonconstant coefficients computes precisely the constant private outputs. Duplicate key/tag pairs give identical generator families, and zero keys contribute no private direction. The final physical witness check uses every indexed column.

For degree s and returned private rank d−t, solve tests either the entire chart cube or a deterministic finite-field seed family from the sibling file pnp-chart-hitting.py. With codimension cap 2(t+2) the candidate list consists of odd sums of at most 2s+1 seeds. On the slice fixing complement anchors and two active sites the two-dimensional residual determinant has degree at most 2s. Search time is 2^{O(s(t+1))} n^{O(s)} for positive s. Search uses the full cube whenever its size already fits the candidate bound. Each realized witness has at most d+2 physical sites.

Run python witness_tests.py for 96 small examples compared to literal physical subset spans at each of three degrees and three structural degree-rank checks. These exercise the direct-cube fallback.

The fixed-height variant in fixed_height.py implements height-aware.md and accepts the extra height_degree argument. The recognizer keeps distinct indexed heights at coincident keys/tags and permits unrestricted Boolean selectors on pure-height columns. Run python fixed_height_checks.py for independent truth-equation image, reconstructed height-degree and literal physical witness comparisons.
