# A cover bound for circuits with zero charge

The Lean theorem `PEqualNP.Outside.L_meta_4186_aux.Q0.complete` proves the positive cover inequality from the inner statement of L-meta-4186 for every graph order when `(orN G C ∖ lam G C).card = 0`. It retains the four original hypotheses. The graph is four-cycle-free with at least one edge, and the circuit is a globally least exact binary AND/OR circuit in top form. The general refutation requested by the official unit remains open.

Write `u` for the number of residual edges, `j` for the number of dirty AND gates, `c` for the number of centreless tops, and `t` for the number of other tops. The proof constructs a cover of size at most `t + u` and proves `2u ≤ j + 2c`.

The main circuit step proves that a dirty AND has at most one distinct reader. The construction retains the gate, substitutes true for its old wire while processing its descendants, and rebuilds the final OR. Two distinct readers would save at least one gate in an exact AO2 circuit that agrees on every input. The counting step assigns each dirty gate to one centreless top. Residual edges accepted by each such top form an induced matching. Choosing one endpoint of each matching edge yields independent inputs, which bound the number of residual edges by the number of available clauses.

The central Lean run produced the following SHA-256 hashes for the endpoint. Compiled object bytes can depend on the build environment.

| Artifact | SHA-256 |
| --- | --- |
| Q0Complete.lean | `a6cbe7e4685c33389e0a118af8ba49da3d3a12cfb33740599d908de7e58fe64d` |
| Q0Complete.olean | `59b583d62e31f517f86d0051c341e6f290ab0eb41862af52adb8e474b77566a8` |

Lean reported the axioms `propext`, `Classical.choice`, and `Quot.sound` for the endpoint.
