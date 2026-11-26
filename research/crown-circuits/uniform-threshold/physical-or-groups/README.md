# Abstracting raw inputs of private OR trees

ThresholdOrGroups.lean operates on the upstream physical indexed monotone circuit model used by GateSurplus.lean. It takes a certificate for the supplied original circuit C. An AND block records the old gate and operand wire indices. An OR block is a binary tree whose internal nodes name real OR gates of C with the specified two operands. Its leaves name raw formal inputs or previously computed block outputs. The certificate allows the original gates of distinct trees to interleave in time. No gate index can be charged twice.

The compiler emits a new physical circuit D. In a group with k raw operand occurrences and t other operand occurrences, replace the raw occurrences by one input bit equal to their disjunction when k is positive. Emit a left-associated chain on these surviving operands. A one-operand result reuses that wire with zero OR gates. A previously computed group root can be read arbitrarily many times. The theorem accounts for actual emitted gates, including their physical indices, and compares Circuit.eval on the two input lists for every assignment in an arbitrary sample domain.

Write K for the total number of raw operand occurrences and V for the number of groups with a raw operand. The exact identity is OR(D)+K = number of charged physical OR gates+V; disjointness of the charged physical indices implies OR(D)+K ≤ OR(C)+V. For K=2n this yields the required 2n−V saving. The function incidence builds the new Boolean input list from lists of raw input indices; pin_real_of_lookup verifies its interface to the compiler.

The decomposition of an arbitrary regular normalized circuit into these certificates, the raw occurrence identity K=2n, and the subsequent threshold-two lower bound are separate results.

The pinned Lean 4.36 kernel replay used the three standard axioms listed in replay.log. Compile GateSurplus first and include its compiled module on LEAN_PATH. [GateSurplus source](../../../seed-obstructions/pinned-surplus/GateSurplus.lean)

The pinned extraction modules construct a forest from a backward binary physical layout and prove that each block checks against the circuit. Count transfer uses the local balance assumption. The book criterion uses the assumption that external roots occur earlier. The five endpoint axiom reports are recorded in extraction-axioms.log. A complete disjoint book with the raw-occurrence count remains a further formalization step.
