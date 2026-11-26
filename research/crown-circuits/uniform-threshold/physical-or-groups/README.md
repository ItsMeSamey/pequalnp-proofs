# Abstracting raw inputs of private OR trees

ThresholdOrGroups.lean operates on the upstream physical indexed monotone circuit model used by GateSurplus.lean. It takes a certificate for the supplied original circuit C. An AND block records the old gate and operand wire indices. An OR block is a binary tree whose internal nodes name real OR gates of C with the specified two operands. Its leaves name raw formal inputs or previously computed block outputs. The certificate allows the original gates of distinct trees to interleave in time. No gate index can be charged twice.

The compiler emits a new physical circuit D. In a group with k raw operand occurrences and t other operand occurrences, replace the raw occurrences by one input bit equal to their disjunction when k is positive. Emit a left-associated chain on these surviving operands. A one-operand result reuses that wire with zero OR gates. A previously computed group root can be read arbitrarily many times. The theorem accounts for actual emitted gates, including their physical indices, and compares Circuit.eval on the two input lists for every assignment in an arbitrary sample domain.

Write K for the total number of raw operand occurrences and V for the number of groups with a raw operand. The exact identity is OR(D)+K = number of charged physical OR gates+V; disjointness of the charged physical indices implies OR(D)+K ≤ OR(C)+V. For K=2n this yields the required 2n−V saving. The function incidence builds the new Boolean input list from lists of raw input indices; pin_real_of_lookup verifies its interface to the compiler.

The following modules derive a decomposition and its raw-occurrence count under explicit physical hypotheses.

The pinned Lean 4.36 kernel replay used the three standard axioms listed in replay.log. Compile GateSurplus first and include its compiled module on LEAN_PATH. [GateSurplus source](../../../seed-obstructions/pinned-surplus/GateSurplus.lean)

The pinned extraction modules construct a forest from a backward binary physical layout and prove that each block checks against the circuit. Count transfer uses the local balance assumption. The book criterion uses the assumption that external roots occur earlier. The five endpoint axiom reports are recorded in extraction-axioms.log.

The later endpoint extracted_book builds a Book C n [] for a backward binary Layout satisfying MeetsInternal, which requires every AND to read only nonraw physical wires. Its CLI axiom report is in branch-axioms.log.

The subsequent kernel-checked endpoints `forest_nodup` and `raw_count_two` give disjoint physical OR indices and K = 2n for the extracted forest. The count assumes a backward binary physical layout, nonraw operands at every AND, and exactly two physical reader occurrences per raw input. The log records `propext`, `Classical.choice`, and `Quot.sound`. These are component lemmas in the threshold proof. Regular normalization and the simple-graph argument require separate formal proofs. [Axiom reports](forest-kernel-receipt.txt)
