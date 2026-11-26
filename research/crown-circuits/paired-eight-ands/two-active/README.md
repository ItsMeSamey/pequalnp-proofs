# Twelve-input threshold two with eight AND gates and two dirty gates

A paired twelve-input threshold circuit of size at most 28 cannot have eight ANDs of which exactly two are true on at least one singleton input, in terminal-clean, minimum-dirty form. The other six ANDs are collected at the output. The mathematical argument combines previously checked neighboring cases with the finite enumerations here. It is not a Lean proof.

## Representation

Give both input ports of every AND a named literal. Each raw receiver and each dirty-gate continuation is represented by the set of ports it can reach using only OR wires. With two chronologically ordered dirty gates followed by six clean terminals, all direction assignments fit in 256 bits. The earliest continuation is T0 and the later continuation is T1. A raw mask has a rejection event obtained by propagating one selected pin of each dirty gate and then reading the six terminal coordinates. Events for a union of raw literals are intersections of their rejection events. Twelve nonempty disjoint events suffice for threshold two.

The transposed binary OR bank has at most 17 paid unions. The paired direct-input normalization lets us assume twelve nonliteral receiver sinks, leaving five helpers, including both nonliteral continuations. The canonical template generator preserves the dirty order and acts by legal input flips and signed permutations of terminal coordinates. Independent terminal-column multiset generation in verify.py recovers the same 403 templates.

If every hot singleton at the earliest dirty gate uses at most one extra literal outside T0 and its two input pins, reattach each such raw as T0 alone or T0 union that extra literal. The corresponding gate can be made a clean terminal without increasing size. For a hard raw K containing both earliest pins, let r count its other literal pins outside T0. Counting source leaves in the union program for T0 and K yields |T0|+r≤6. Thus width at least five always reduces to the separately excluded one-dirty case. At equality the protected sets use separate optimal union trees and exhaust the five helpers. These are the earliest-cleanup and protected-source arguments in the seven-AND two-dirty certificate.

## Finite cases

| Earliest width | Templates | Initial roots | Forwarded roots | Helper search nodes | Volume-passing libraries | Packings |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 23 | 588 | 261 | 12,983,295 | 1,370,402 | 0 |
| 2 | 49 | 554 | 135 | 677,423 | 40,045 | 0 |
| 3 | 70 | 196 | 10 | 16,681 | 1,601 | 0 |

Width four uses the saturation search over 79 templates, 1,038 hot anchors and 233,550 ordered tree pairs. Of these, 19,462 passed the volume bound and none packed twelve events. Repeating this full search with the terminal parity predicate disabled gave identical counts. The width-three saturation crosscheck tested 782,460 tree pairs on 2,484 anchors and found no packing. Widths five through eight contain respectively 76, 62, 38 and 6 templates.

For each pair of clean comparisons, both relative sign parities must occur among the chosen raw singletons that activate an arm on each comparison. If an orientation lacks a witness, replace the two terminal comparisons by one comparing the ORs of the aligned arms. The circuit grows on positive inputs, remains false on every singleton, uses no more gates, and lands in the separately excluded seven-AND case with at most two dirty gates. The packing search requires all thirty parity witnesses. Subset dominance only discards a raw candidate if its replacement also retains every covered parity.

For a fixed hard K, the prescreen checks the transpose cost of demanding T0,T1,K and a fourth proposed raw. It relaxes all other sharing, and in the width-one and width-two runs returns possible whenever its packing recursion exceeds the work bound. These positive prescreen outcomes all go to the exact library search. The exact search constructs helpers within the three protected roots before helpers outside them. Outside helpers cannot be operands of an inside helper under union. At each step the signed-axis symmetry fixes both ordered dirty gates, their continuations, K and every previously chosen helper individually. Strict union inputs have smaller literal cardinality. The final stage checks all one-union raw candidates and searches for eleven more disjoint events alongside K.

An additional width-one run used separately reviewed minimum-dirty straddler constraints and unmarked-axis folding. It found zero in 9,215,694 nodes and 67,108 volume-passing libraries. The primary table uses the completed plain library checker without those extra constraints. The calculus desk reviewed the template symmetries, saturated trees, search order, helper-cost conditions, permissive prescreen and parity-aware dominance. The two independent width-one runs use different pruning with a common representation.

## Replay

Run replay.sh with a C++20 compiler and Python 3. verify.py checks the stored ledger coverage independently, including all forwarded root identities and all physical template IDs. The neighboring prerequisites are the A8 one-dirty result in calculus/eight-one/certificate and the A7 two-dirty development in reductions/seven/two-dirty.md. The latter also records the source-count and cleanup arguments. The paired direct-input normalization is recorded in reductions/seven/direct-split.md.
