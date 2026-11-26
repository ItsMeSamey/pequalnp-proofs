# Threshold two at every arity

For minimum binary monotone AND/OR circuit size with unrestricted fanout, **C(n) = 2n + √(2n) + Θ(n^(3/10))**. The two bounds hold with positive absolute constants for all sufficiently large n. The proof determines the order of the third term. Its optimal coefficient remains open. Independent mathematical reviews checked the unrestricted lower bound and its prerequisite arguments. [Lower bound](unrestricted-matching-exponent.md) · [Upper construction](three-level-matching.md)

The refined construction gives C(n) ≤ 2n + √(2n) + (5/4)2^(9/10)n^(3/10) + O(n^(7/30)). This coefficient is an upper bound on the unrestricted optimum. [Short-signature construction](short-signatures.md)

The unrestricted liminf of (C(n)−2n−√(2n))/n^(3/10) is at least the algebraic constant approximately 1.15238806926. Independent mathematical reviews checked the corrected private-receiver bound, including the additive five-gate allowance, and the optimization over both receiver classes. The first sentence of the frozen optimization manuscript refers to the private-pins lemma. Its dependency is the corrected version linked here. [Corrected private-pins lemma](unrestricted-private-pins-v2.md) · [Coefficient optimization](unrestricted-private-moment.md) · [Earlier two-class bound](unrestricted-block-moment.md)

## Earlier bounds and constructions

The matching construction gives **C(n) ≤ 2n + √(2n) + O(n^(3/10))**. Together with the lower bound below, this gives **C(n) = 2n + √(2n) + O(n^(3/10))**. The proof counts matching signatures and gives a deterministic finite search for a suitable graph. The final theorem above gives a matching order of growth for the remainder. [Construction](matching-signatures.md)

For n ≥ 4, the minimum number C(n) of fan-in-two monotone AND/OR gates with unrestricted fanout satisfies **C(n) ≥ 2n + (√(8n−7)−7)/2**. The frozen manuscript received independent mathematical proof reviews. Combined with Theorem 9 of Krapivin, Przybocki and Subercaseaux, this gives **C(n) = 2n + √(2n) + O(n^(1/3))**. The full proof is a mathematical manuscript. [Proof of the stronger bound](shared-or-cut.md) · [Upper bound](https://doi.org/10.4230/LIPIcs.SAT.2026.23)

## Earlier all-arity bound

For every integer n ≥ 2, a binary monotone circuit for threshold two requires at least 2n + (4/3)√(n+3) − 6 gates. Four independent mathematical reviews checked the manuscript, including the component accounting, the star restriction and the induction. [Proof](threshold-lower.md)

Sergeev's lower bound is 2n + √((2n−4)/3) − 19/6. The coefficient of √n in the lower bound increases from √(2/3) to 4/3. Theorem 9 of Krapivin, Przybocki and Subercaseaux gives an upper bound of 2n + √(2n) + O(n^(1/3)). [Sergeev](https://doi.org/10.4213/dm1547) · [Krapivin, Przybocki and Subercaseaux](https://doi.org/10.4230/LIPIcs.SAT.2026.23)

## Remainder in the matching construction

If the two incidence layers are counted separately and the tail computes threshold five on all w vertex signals, the resulting gate ledger has an Ω(n^(3/10)) remainder. This proves sharpness for the specified construction. The unrestricted lower bound above uses an additional structural argument. [Gate-count proof](matching-ledger-lower.md)
