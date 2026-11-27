# Complete private two-hot sector with seven outer ANDs

Assume the normalized minimum representation has seventeen sites, one inverter, a fully private prefix computing an OR of two distinct raws, and seven outer AND gates. The outer portion has eight OR gates, and its zero clamp F0 loses at least one OR. Every hot raw's positive cofactor is computed by F0. The positive cofactors of 0,1,2,3,4 each require eight ORs, so both hot owners lie in {5,6,7,8,9}. The ten unordered pairs are exhausted as follows.

| Pairs | Conditional exclusion and source |
|---|---|
| 56, 78 | Seven-edge double-deletion tree with a tight four-vertex path and a wire true at opposite endpoint singletons; private-59-89.md. |
| 57, 58, 68 | Both adjacent owners have only AND readers in F0; their edge forces a common product plus separate readers, beyond the zero-deletion budget; private-or-pair.md. |
| 59, 89 | Eight-vertex path on double deletion. Four leaf restrictions give the same two-OR path obstruction; private-59-89.md. |
| 67 | Ten-gate double minor consisting of a five-cycle with a pendant plus an isolated edge. A forced internal positive singleton contradicts the budget upon activating an isolated-edge endpoint; private-67.md. |
| 69, 79 | Fourteen-gate signed single deletion with a raw-9 inverter. A forced positive singleton in its raw-9 guard contradicts the eleven-gate monotone double deletion; private-or-pair.md. |

The sources track raw aliases, specialized signals and gate losses separately. The ten-pair result does not cover private masks with six outer ANDs, raw inversion masks or nonprivate prefixes.
