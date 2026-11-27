# Equality guard with an interior value read

Use four forward rails numbered 0,1,2,3, with r=(0 1 2). In order, install r^x, the transposition (2 3)^A, the transposition (1 3)^B, r^(−q), and fixed feedback (0 2). Mark rail 3 immediately before the first switch and rail 0 immediately after it. Each of x and q is used once.

With permutations acting right to left, the return at the first seam is (0 2) r^(−q) (1 3)^B (2 3)^A r^x. The upstream coordinate of the interior mark is r^(−x)(0). The two marks join in precisely the following cases, listing the four bit pairs (x,q) in order 00,01,10,11.

| A | B | Joined outputs |
|---|---|---|
| 0 | 0 | 0,0,0,0 |
| 0 | 1 | 0,0,0,1 |
| 1 | 0 | 1,0,0,0 |
| 1 | 1 | 1,0,0,1 |

Both mismatch settings reject regardless of both verifier outputs. With agreement, zero selects A and one selects B. Any independent two-port verifier can occupy the A or B stage if its identity and swap outputs are interpreted as zero and one. In particular disjoint deterministic read-once clause formulas may be composed using deterministic-two-clause-core.md. For existential verifiers, the table applies to each individual physical setting, and disjoint controls permit compatible settings to be combined. The checker realizes both transposition stages by native three-cycles with private third-socket returns and checks all sixteen physical inputs.

When A is the complement of a third bit z and B equals z, the two middle stages together are (2 3) for z=0 and (1 3) for z=1. The relative permutation is a single three-cycle. One native switch and fixed wiring therefore implement the combined stages, yielding an exact deterministic all-three-equal marked-pair test.

## Limitation of exporting a ternary signal

Consider the different interface which exports three ports G,P,N, requiring identity in both mixed cases, (G P) at 00, and (G N) at 11. Each of x,q has just one native switch; arbitrary fixed internal wiring is allowed. Closing the three output ports to their corresponding inputs identifies this signal with the first-return permutation on three marks.

Rebase the circuit at the mixed corner 01. Let the single flip producing (G P) be h and the one producing (G N) be k. At the reference all three marks have separate orbits. The isolated-mark flip lemma from private-sign-satellites.md implies h avoids the physical orbit of N: both before and after h the mark N is isolated, while the other two marks change their first return. The flip k must meet the orbit of N, since otherwise that orbit would remain fixed. Now enable h alone: the physical orbit of N remains exactly the original one. Flipping k from this setting must restore identity at the other mixed corner. Thus k touches the orbit of N while keeping N isolated and changing the return on the other two marks, contradicting the same lemma. This impossibility concerns the exact exported three-port signal with fixed hidden wiring. The marked-pair guard above uses a different interface.
