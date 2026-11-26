# Eventual lower bound for the third term of threshold two

For each real ε > 0 there is a cutoff N independent of the circuit. For every n ≥ N and every monotone circuit of fan-in at most two computing threshold two on the full Boolean cube, put z = size − 2n − √(2n). Then z ≥ 0 and (9765625 − ε)n³ ≤ 2048 z¹⁰. Consequently the limit inferior of the normalized surplus z/n^(3/10) for minimum circuits is at least 5/2^(11/10).

The original pinned kernel build checked [circuit_lower_sharp](sources/ThresholdSharpNativeLower.lean) under propext, Classical.choice and Quot.sound. This package locks all 268 local and project sources. An independent clean replay rebuilt all 268 sources, including six PEqualNP modules, and reproduced the axiom report. Each local import resolved to a freshly built object. See the [receipt](independent-replay/receipt.json) and [verification result](independent-replay/independent-check.txt). The coefficient upper bound is a separate question.

[Portable source manifest](ThresholdSharpNativeLower-manifest.tsv) · [Compiler axiom report](axioms.log)
