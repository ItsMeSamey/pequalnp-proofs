# Reviewed q=3 single-entrance bound for L-meta-6648

On the original eleven-vertex graph and under the issued size, leastness, TopForm and junk-count hypotheses, suppose q=3 and exactly one physical OR receives a dirty AND as a direct input. Then |Ustar|≤2c+j+3. The cardinal balance transfers the conclusion to the issued sets. A gate counts once even when both its inputs come from dirty ANDs. Different downstream OR gates can inherit the mixed signal. This includes the case of exactly one exceptional OR with AND ancestry.

The wrapper 6648-q3-one-entrance-review.md records the original-circuit split. Its provisional numerical status is superseded by the frozen replay below. Its clean-AND index pins the supporting case files. The original graph/cofactor and q=2 precedents are available in the prior research packets g11-21-research.tar.gz (04c211da6c33cf649e73efed06e1a665f18c1cfa0b89a845d7f29d54eedbceab) and g11-6648-q2.tar.gz (84a36658cc377df6339006eca75ac56f152c06db6dbde69fba19f1d6cf6a8f09). These reports concern mathematical deductions under the original hypotheses. A combined Lean certificate for this theorem is outstanding.

| H8 maximum | Evidence |
|---|---|
| F(1,1)≤2, F(1,3)≤5 | singleton_h8_one_exception_three_batches.md |
| F(1,2)≤4, F(1,4)≤7, F(1,5)≤9 | Allocate each marked edge once and apply the preceding bounds to disjoint subcollections. Removing other marks preserves the common exceptional support and enlarges admissible anchor choices. |
| F(2,1)≤3 | bounds_6648_h8_two_exceptions_one_product.md |
| F(2,2)≤5 | Independent checker rejected all 462 six-edge masks. |
| F(2,3)≤6 | Independent checker rejected all 330 seven-edge masks. |
| F(2,4)≤8 | 6648-h8-F24-two-unmarked.md |
| F(2,5)≤9 | 6648-h8-F25-one-unmarked.md |

The checker is twin_6648_h8_replay.py. The two complete rows appear in twin_6648_h8_results.jsonl, SHA-256 f4a9aebc7091f57a8afde66c5d4aac34bf3c024a9cfaaddbc0bdfe4fe10f00ea. The dedicated seven-edge file has SHA-256 b561de3ffd83c6ce3437edf2eb7e29323115aca1c0d954ef85cf1e67538a2570. The two analytic notes for the same two rows are supplementary. The finite calculations are independent of the separate H8 ownership SAT encoding.

Both independent review teams approved the entire wrapped theorem and finite evidence. Their signoff binds 6648-q3-one-entrance-review.md, SHA-256 1231d3c9a9d111a5ac4d1b47b7187f515823db29830170536c62cf82fe7d4a25, and premises_6648_q3_one_physical_index_v2.md, SHA-256 5c827a90a625210612ebe1107d662f80d670dd89964f7ff34cae48181e4264d2.

The two precommitted positive controls were feasible under the same checker: four-edge mask 270 with two batches and one exception, and single-edge mask 1 with one batch and one exception. The frozen control receipt has SHA-256 e9eee809b839120f5a6833be68db920b01052b827ed663bc878c9316c966ce83.

The final independent replay also exercised every one of the seven nonredundant numerical rows. All 1,815 masks were infeasible, and exact mask sets were checked in each row. The full seven-row ledger twin_6648_h8_all_thresholds.jsonl has SHA-256 8758a4598770d110d9c694e7df70928646d1cb26ba980560d04e42f20784b92e. The two earlier rows remain as an immutable checkpoint.
