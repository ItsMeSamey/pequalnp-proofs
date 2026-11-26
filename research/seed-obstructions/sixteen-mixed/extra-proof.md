# Mixed circuits after fixing nine point boundary signatures

For a connected binary circuit with m mixed gates and t distinct boundary signals, the number of input-edge uses beyond one per non-output signal is m−t+1. Topologically construct the circuit with a frontier. Ordinarily replace two selected frontier signals by a gate. Whenever a selected operand has a later use, retain it on the frontier; retaining either operand spends one extra use, and retaining both spends two. This realizes a signal of any allowed fanout. A gate with identical operands can be deleted. The checker allows both operations at every gate with mixed ancestry, including gates that simplify semantically.

Keep the actual point and line functions on positives, where both side inputs are singletons. On a negative their values can only decrease when replaced by the disjunction of the corresponding singleton signatures. Thus a compatible mixed circuit separates the canonical row vectors. At every frontier every positive/negative pair must be distinguished by a frontier occurrence. An obligation distinguished by both selected operands survives their AND or their OR. An obligation distinguished by neither survives through another wire. Only the pairs uniquely distinguished by a consumed operand can be lost. This yields an exact pruning condition at every step. Merging equal multisets of sampled truth tables, ancestry sides and spent-use counts preserves future reachability. If the frontier collection is empty before the last gate, any separator of that size is excluded.

The 24 permutations used by the verifier preserve both the 28 positive and the 245 maximal negative raw side vectors. It checks that equality from the decoded formal statement for each permutation, and permutes the line signatures together with the point signatures. The point-circuit gate-cost bound is calculated on each original family before the symmetry reduction; the search on canonical boundary wires only needs the sampled row sets to be invariant.

| Mixed gates | Point / line boundary counts | Point charge cutoff | Extra uses | Cases | Representatives | First empty frontier, with unweighted representative counts |
| --- | --- | --- | --- | --- | --- | --- |
| 16 | 9 / 7 | 17 | 1 | 1,041 | 65 | 6 (5), 8 (12), 10 (40), 11 (8) |
| 17 | 9 / 7 | 16 | 2 | 123 | 9 | 9 (2), 11 (7) |
| 17 | 9 / 8 | 15 | 1 | 435 | 29 | 7 (8), 8 (11), 9 (5), 11 (5) |

The 18-mixed case with nine point and seven line signals has 15 eligible point families, two orbit representatives, and three extra reads. Both representatives die after gate 12. The point lower bound of 15 rules out every larger mixed budget with nine point signals. Together with the 16-gate read-once case and the preceding structural arguments, every residual solution of total size 33 must have at least ten point boundary signals.

In the 17-mixed row with eight line signals one pure line gate is available. The seven raw lines and this gate must supply the eight distinct line functions. The extra signal is a conjunction or disjunction of two raw inputs, so its singleton signature has size at most two. The search tests every such signature including the empty set and all singleton repetitions.

Place verify_extra.py alongside verify_packing.py and L-meta-18968.json and run it with the charged family table as an argument. A second argument limits the replay to one row, e.g. 17-P9L7. The 16-gate row is additionally confirmed against a C++ verifier that distinguished functions on every assignment of the sixteen boundary bits.
