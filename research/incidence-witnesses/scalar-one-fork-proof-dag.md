# One fork in a native physical proof

On an original flag select one true operand per visited OR and both pins per visited AND. Retain only vertices reachable backward from the output after these choices and keep one vertex per physical signal. A fork is a nonraw vertex with at least two retained outgoing pin uses toward the root. Raw pins count physical operand slots reading the two original raw labels.

Fix a set G of k candidate forks and form ordinary all-uses cofactors C[g←1] with shared extra gate counts X_O,X_A as in scalar-all-occurrence-cofactor.md. Count the flags having a ≤4-leaf proof, or a native proof DAG with at most four raw pins and at most one fork, which if present belongs to G. For q≥4 their number is at most

45O+83A−44N+22 +45X_O+83X_A+128k.

Append the terms F_g AND C[g←1] by OR to the scalar. Each term implies the original scalar because pinning a true g does not alter evaluation. Include at most one additional AND and one OR per candidate. Without a fork the proof unfolds without repeating a physical raw pin. With the single fork g, use its local proof once and replace every outgoing occurrence of g by one in the remainder. After cutting these edges every other nonraw vertex has at most one retained outgoing pin. Each such vertex therefore contributes at most once to the combined local and residual proof, and the total raw occurrences across the two are at most the original four pins. Folding the pinned remainder's constants only shortens the witnessing proof. The adjoined term thus accepts on a ≤4-leaf proof, including if the remainder is constant one. Apply the numeric four-leaf bound on the enlarged scalar, giving the displayed budget. Different flags may choose entirely different sub-DAGs in the same original highly shared circuit.

A site g with cofactor folding to one requires no cloned rows and its terminal term can simply be F_g; cost is one OR, hence 45 in this estimate. This captures arbitrarily many occurrences of a single sufficient four-leaf witness. There is no conclusion for unrestricted fork patterns or general expensive cofactor costs.
