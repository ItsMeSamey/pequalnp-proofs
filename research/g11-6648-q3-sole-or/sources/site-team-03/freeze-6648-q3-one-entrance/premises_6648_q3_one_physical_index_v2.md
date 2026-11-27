# L-meta-6648 q=3, clean sole x AND, one physical dirty-reading OR

Original size 21, least TopForm, x=3, A=x AND S sole x reader and clean, j≥3. Exactly one OR M has a physical dirty AND pin below the clean tops. Count original residual edges. This index excludes a second such OR. It uses the original reader classification, common-OR theorem and anchored-corner footprint bounds invoked in the listed proofs. The target is U≤2c+j+3.

Write F(e,k) for the maximum number of original residual H edges covered by k clean projected conjunctions using up to e common exceptional disjunctions. All batches use the same library. H deletes 3,6,7. A binary exception joins guarded terminals, and a second can also join the first to a guarded terminal. The bounds used at k=1,2,3,4,5 are respectively (2,4,5,7,9) at e=1 and (3,5,6,8,9) at e=2. These are upper bounds, not claims of equality. The finite component is conditional on independent replay. No projected circuit is assumed least.

| Original branch | Proof filename below | Finite inputs |
|---|---|---|
| Pure S | one_exit_remaining_positive_m | none |
| Positive raw impure S, positive M | shared_projection_scope | F(2,1..5) |
| Positive raw impure S, empty M | shared_projection_scope; empty_tap_three_junk | F(1,2..5); c=0,j=3 boundary analytic |
| Empty S, positive M | one_exit_remaining_positive_m | F(2,1), F(2,3..5); D=S uses monotonicity at smaller batch counts |
| Empty S, empty M, no positive exit directly reading M | one_empty_exit_empty_S | F(2,1..5) |
| Empty S, empty M, one or two positive exits, S=M | one_empty_exit_empty_S | F(1,2..5) |
| Empty S, empty M, S differs from M, two positive exits | one_empty_exit_empty_S | anchored footprints, no positive-exception DP |
| Empty S, empty M, S differs from M, one positive exit | one_empty_exit_empty_S | one near star uses anchored footprints; two or more near stars uses F(1,2), F(1,4), F(1,5) plus sparse analytic argument |

For positive raw impure S, M feeds S along an OR-only path. Tracing S backward through OR inputs to the first dirty pin identifies the unique physical entrance M. Empty M must directly read two dirty ANDs since an earlier raw-empty OR would itself require another entrance. Filenames in the table have prefix premises_6648_ and suffix .md. The appendix pins the files as inspected along with prototype sources and receipt.
76744d3e2f93b22cc53894bca29c9bc71f4eb60c799e551bc569d37bd3f26022  premises_6648_shared_projection_scope.md
77f03a0788936f6d941b3b1066139974b30efed79d855a440d4b33a30a96c58b  premises_6648_empty_tap_three_junk.md
0951bc77dbd77c83eb8a01e23ca03e89e9c999b6daccc93f75615141b9bf98fb  premises_6648_one_exit_remaining_positive_m.md
be7b23c6559b8d11ab82fcd1150ff8857d74e8cf229ff784f1d8a9fb6350b90d  premises_6648_one_empty_exit_empty_S.md
a696557b699d09d077de882b325803b157364f9c9b44844e7b28301f2b74e6e2  premises_6648_projection.py
a942348f44ba9be8b364c3f097a388b5e2a532983364c87e332b93adec1250f0  premises_6648_projection_shared.py
be5dd6934b40c32618163b32e9b62151f6b9ec03782cbe1e71eee0da0dfd1030  premises_6648_projection_prototype_receipt.txt
