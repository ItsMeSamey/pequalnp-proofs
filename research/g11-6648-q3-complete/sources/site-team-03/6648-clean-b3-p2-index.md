# Clean sole AND at vertex 3, three direct entrances of which two are raw-positive

Fix the original least size-21 TopForm G11 circuit, j≥3, q=b=3. All three exceptional ORs directly read a dirty AND, and exactly two have nonempty raw support (p=2). The sole reader at vertex 3 is the clean AND A=x∧S. The original residual count satisfies U≤2c+j+3.

| Original sibling S | Proof |
|---|---|
| Nonempty raw support | [Visible sibling proof](6648-clean-b3-p2-visible-complete.md). Zero taps contradict the common-OR classification. The external-reader requirement on the exact cards excludes two taps. At one tap the other positive receiver directly reads S, and the H projection gives U≤2c+6. |
| Empty raw support, AND | [Empty sibling dispatch](6648-three-direct-clean-empty-s-index.md), section “S an AND”, and its [dirty AND proof](6648-three-direct-clean-empty-s-dirty-and.md). The raw-empty sibling accepts both near singletons, so it is dirty. |
| Empty raw support, OR | Impossible. The empty sibling dispatch supplies an external paid OR reader of S. S itself is a raw-empty paid entrance. Its reader has to be a different direct entrance, hence its other pin is a dirty AND and contributes no raw leaf. This would require a second empty receiver, whereas p=2 leaves exactly one. |

A primary input has nonempty raw support and cannot accept both near singletons. The split therefore exhausts the specified physical signatures. The card floors, graph footprint bounds and original-star conventions are the ones identified in the referenced proofs. This is a source dispatch; it has no combined Lean receipt.

| Source | SHA-256 |
|---|---|
| 6648-clean-b3-p2-visible-complete.md | d8a15dfc8811d7df6563072ab05456260da0313266f3ef829cd38c55c4ff74c1 |
| 6648-three-direct-clean-empty-s-index.md | f174a7125977bcc1675c2780b84cdfbc8fcc8e44a3a2790976ece0053aec0acc |
| 6648-three-direct-clean-empty-s-dirty-and.md | c8c6fe51a8d0336a24db029d9467f5982acb9953c58845b70a92d99718b6942a |
