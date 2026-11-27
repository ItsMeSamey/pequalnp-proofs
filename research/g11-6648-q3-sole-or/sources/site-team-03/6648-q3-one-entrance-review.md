# L-meta-6648 for q=3 with one physical OR reading a dirty AND

Take the original L-meta-6648 graph, least TopForm circuit of size at most 21, and at least three junk ANDs. Suppose q=3 and exactly one physical OR has a junk AND as an operand. A gate with two such operands counts once. Other ORs can receive the mixed signal through earlier ORs. Let j count the junk ANDs and c the centreless tops. The target of this reduction is |Ustar|≤j+2c+3. The issued selected-set inequality then follows from the exact cardinal balance alone.

The reviewed cofactor floors and reader classification give size 21 and exactly one reader of input 3. The following proof files are relative to this directory.

| Input-3 reader | Further split | Source and SHA-256 |
|---|---|---|
| OR | Sibling is a dirty AND | singleton_6648_q3_donor_analytic.md, 1dde1c5021fb7ba3d5165fd51822c153e703d72772d382895a5abc9d95c9f5e9 |
| OR | Sibling is a raw-empty OR | singleton_6648_q3_empty_or_sibling.md, 1dbd6cc8713f1ec8b8c66d16126e45bda885c79bb33510b09a8de7dd98617a57 |
| Dirty AND | Both possible input types at the unique receiving OR | bounds_6648_q3_single_exit_dirty_and.md, 4b91df20f68d3d9d3dfc0ba43c6af29a73a59bcc32c47f163830662a7f337a88 |
| Clean AND | Eight cases on its other operand and the receiving OR | premises_6648_q3_one_physical_index_v2.md, 5c827a90a625210612ebe1107d662f80d670dd89964f7ff34cae48181e4264d2 |

The sole-OR sibling is singleton-negative by the graph's original input-3 toggle. TopForm and the first dirty-AND/OR boundary give the two stated sibling cases. Original-circuit leastness supports the removal of equivalent gates. The clean-AND proof uses a common exceptional-support library when allocating residual core edges to multiple projected products. Its finite bound concerns the induced graph after deleting vertices 3, 6, and 7. It is logically separate from the 30 ownership certificate cells used in seeking a compact proof of the eight-input cofactor lower bound.

At assembly the clean-AND finite bound still awaited authorized independent numerical replay. No combined Lean proof has been checked. Use the original hypotheses in every branch; search models without established leastness must remain eligible.
