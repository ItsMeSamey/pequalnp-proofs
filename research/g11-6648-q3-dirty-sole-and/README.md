# G11 surplus bound for a dirty sole AND reader and three exceptional ORs

In the issued L-meta-6648 setting, assume input 3 has exactly one direct reader, a dirty AND. Let `j` count dirty ANDs, `c` count centreless tops, and `q` count the gates in `orN` outside `lam`. For `q=3`, the number `U` of original residual graph edges satisfies **U ≤ j+2c+3**. The issued balance `|X|+j=U+|J|` then gives `|X|≤2c+|J|+3` for the original selected edge and gate sets.

The original hypotheses include a least AO circuit realizing the specified eleven-vertex graph, size at most 21, TopForm, and `j≥3`. The cited lower bound makes its size exactly 21. The complete issued statement, including the graph and all selected-set, ownership and disjoint-witness conditions, appears in `statement/issued-6648.lean.txt`. It is a copy of the problem statement with its original proof placeholder. This packet proves the stated dirty sole-reader slice at source level. A combined Lean kernel verification is outstanding.

## Proof dispatch

The deleted input has sole reader `g=3∧S` followed by the charged OR `M=g∨D`. Let `b` count distinct **physical OR gates** with a dirty AND as a direct input, in the original pretop circuit. Two dirty input pins at one gate count once. The mandatory M gives `b≥1`; every such gate is charged, so `b≤q=3`. Routing and reconvergence after a gate do not increase this count. These three files exhaust the result.

| b | Reviewed source | SHA-256 |
|---|---|---|
| 1 | `bounds_6648_q3_single_exit_dirty_and.md` | `4b91df20f68d3d9d3dfc0ba43c6af29a73a59bcc32c47f163830662a7f337a88` |
| 2 | `6648-q3-dirty-two-direct-complete.md` | `3c238d0dca24d33817c8124c8ee41fd20b6b3ced424aa4dc652bcf3331679a70` |
| 3 | `6648-q3-dirty-three-direct-complete.md` | `ab31eeabf5d860c1f5f9050dd90ba1f24317943acd22fce77bf565fe447a618f` |

Teams 07 and 08 independently issued source-review GO for each of these exact hashes. They checked the physical reader cases in the original circuit, how the minimum 19-gate cofactor changes the supplier of an OR pin, the guarded projections and the tight parameter bounds. The review did not execute a combined Lean theorem or add new numerical cases. Original stars and residual labels are retained across restrictions; projected circuits are used as least circuits only when the original 19-gate lower bound and the exact two deletions justify it.

## Dependencies

The local source notes beside this README include the two-input and three-input case refinements, the protected donor argument, the anchored-clause and matching arguments, and the G11 footprint, single-star and size reductions. The immutable parent research archives are included under `parents/` so the prior proofs, historical receipts and certificate sources used by the reductions travel with this release.

| Included parent | Use | SHA-256 |
|---|---|---|
| `g11-21-research.tar.gz` | Size-21 theorem, card and eight-vertex core sources | `04c211da6c33cf649e73efed06e1a665f18c1cfa0b89a845d7f29d54eedbceab` |
| `g11-6648-q2.tar.gz` | Reader structure, donor masking and protected two-deletion matching bounds | `84a36658cc377df6339006eca75ac56f152c06db6dbde69fba19f1d6cf6a8f09` |
| `g11-6648-pure-or-empty.tar.gz` | Raw-empty reduction, exclusive anchored-double footprint, P=14 one-star elimination and earlier reviewed sources | `75b48f66c04e6fac566cdab46c829983a7243606aaba9d843e3f65e465efcb6b` |
| `g11-6648-q3-one-entrance-full.tar.gz` | Earlier complete single-direct-entrance packet and its independent replay ledger | `9a4d4047ae2d3874a263ddb00a00f0be40ce897c5585837d3081df24d8629014` |

For the size reduction at `P=j+2c+q`, an ordinary top stars at least one edge and hence `U≤15`. Only `P=14,U=15` needs the single-star exclusion. With no ordinary top the separate aggregation count gives `P≥22`. These are original-circuit bounds. The footprint used when `U≥8` additionally needs the absence of a starred edge at input 3, supplied by its dirty sole AND reader.

To verify archive integrity, extract it and run `sha256sum -c PAYLOAD.sha256` inside the extracted directory. The manifest verifies the proof text, the issued statement, and each parent archive byte for byte. The parent scripts and receipts document their original verification environments; checking these hashes requires only a standard SHA-256 utility.
