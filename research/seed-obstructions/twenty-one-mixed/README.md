# Twelve point and ten line wires at twenty-one mixed gates

A residual separator of size at most 33 with exactly 21 mixed gates cannot have twelve point-boundary wires and ten line-boundary wires. The connected mixed region in this allocation is read-once. The [portable certificate](W12L10-verified.zip) includes the pinned input, C++ search, inherited point-cost data, proof and replay instructions. An independent reviewer extracted the archive and reproduced all 345,810,125 incompatibility checks. The exclusion concerns this allocation; existence at twenty-one mixed gates remains open.

With eleven point wires and nine line wires, the nine-paid equality search and the ten-paid nonlocal point obstruction leave 354 star-local ten-paid point banks and 540 two-gate line banks. Their 191,160 labeled combinations give 8,466 simultaneous symmetry representatives. Every frontier is empty by gate eleven. The independent audit regenerated the domain and representatives and checked the recorded depth counts. [Replay and case data](point-equality-frontier/README.md)

## Complete width grid

Every separator of total residual size at most 33 on the pinned sample requires **at least 22 mixed gates**. The archive includes the width-by-width argument, checker packages and a SHA-256 manifest. Extract it and run `sha256sum -c SHA256SUMS` from its root. The independent W12/L9 replay exhausted 56,519,680 pairs. The independent W12/L8 price-nine four-label replay exhausted 305,306 canonical pairs. Both returned zero survivors. The unrestricted existence of a separator at size 33 remains open. [Complete grid](complete-grid.zip) · [Earlier mixed-gate bound](../twenty-mixed/README.md)

In the stated minimum terminal-clean normalization at this budget, at most twelve clean terminal AND gates suffice. With the additional tie breaks specified in the proofs, at least five dirty mixed gates and three wires between dirty gates are necessary. [Terminal count](thirteen-terminal-proof.zip) · [Dirty gates](four-dirty-proof.zip) · [Dirty wires](sparse-prefix-proof.zip)
