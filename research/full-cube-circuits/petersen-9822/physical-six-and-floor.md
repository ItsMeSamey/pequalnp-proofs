# Six AND gates are necessary for the original ten-input graph

Every physical monotone circuit in the stated binary AND/OR gate model that computes the listed 13-edge graph function on all 1,024 input assignments contains at least six AND gates. The circuit may use any number of OR gates. The theorem quantifies over the original gate list and output index.

Lean proves `Research.Graph9822.FreeOR.physical_six_and_floor` by reducing a hypothetical circuit with at most five ANDs to a normalized witness with either two or three hidden products. Both cases are excluded. The original two-hidden-product endpoint passed at 10:41:22 UTC, followed by the six-AND theorem at 10:41:25 UTC. The terminal reports list `propext`, `Classical.choice` and `Quot.sound`.

The independent audit paired 1,372 project modules and 13 external imports. The theorem source has SHA-256 `f044218af97440f2ef6e078d0305114a7679f409de4d8c6f0dfe507137cd0fd7`, and its compiled object has SHA-256 `e0d477e1de950e23fd90888ae2d4930aeedf4cf6cf0b5d24f79eafd6cbc97b1d`. Extract the kernel archive and run `sha256sum -c SHA256SUMS`. The list hash is `edbaf15dc45591984575f35b334e48f0f5aaed225974fd6937c9941f9af12168`. Publication repeated this check after extraction; the theorem's kernel verification comes from the recorded Lean build.

For the full size-17 question, the monotone case with exactly six ANDs and at most eleven ORs and the low-AND one-NOT case remain open in the formal proof.
