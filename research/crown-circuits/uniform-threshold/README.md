# Threshold two at every arity

For the minimum size of a binary monotone AND/OR circuit with unrestricted fanout computing threshold two on all n-bit inputs,

    C(n) = 2n + √(2n) + (5/4)2^(9/10) n^(3/10) + o(n^(3/10)).

The lower bound matches the coefficient of the three-level construction. Two independent mathematical reviews checked the frozen lower-bound manuscript and its use of the earlier unrestricted argument. The full asymptotic theorem has mathematical proof review. [Sharp lower bound](unrestricted-sharp-receiver.md) · [Matching construction](three-level-matching.md) · [Codegree estimate](matching-codegree-constant.md)

The construction also gives a one-sided upper error of O(n^(7/30)). [Refined construction](short-signatures.md)

The earlier unrestricted lower bounds of order n^(3/10) and the private-receiver coefficient approximately 1.15238806926 are retained below. [Order of the third term](unrestricted-matching-exponent.md) · [Private-receiver bound](unrestricted-private-pins-v2.md) · [Earlier coefficient](unrestricted-private-moment.md)

## Earlier bounds and constructions

The matching construction gives **C(n) ≤ 2n + √(2n) + O(n^(3/10))**. Together with the lower bound below, this gives **C(n) = 2n + √(2n) + O(n^(3/10))**. The proof counts matching signatures and gives a deterministic finite search for a suitable graph. The final theorem above gives a matching order of growth for the remainder. [Construction](matching-signatures.md)

For n ≥ 4, the minimum number C(n) of fan-in-two monotone AND/OR gates with unrestricted fanout satisfies **C(n) ≥ 2n + (√(8n−7)−7)/2**. The frozen manuscript received independent mathematical proof reviews. Combined with Theorem 9 of Krapivin, Przybocki and Subercaseaux, this gives **C(n) = 2n + √(2n) + O(n^(1/3))**. The full proof is a mathematical manuscript. [Proof of the stronger bound](shared-or-cut.md) · [Upper bound](https://doi.org/10.4230/LIPIcs.SAT.2026.23)

## Earlier all-arity bound

For every integer n ≥ 2, a binary monotone circuit for threshold two requires at least 2n + (4/3)√(n+3) − 6 gates. Four independent mathematical reviews checked the manuscript, including the component accounting, the star restriction and the induction. [Proof](threshold-lower.md)

Sergeev's lower bound is 2n + √((2n−4)/3) − 19/6. The coefficient of √n in the lower bound increases from √(2/3) to 4/3. Theorem 9 of Krapivin, Przybocki and Subercaseaux gives an upper bound of 2n + √(2n) + O(n^(1/3)). [Sergeev](https://doi.org/10.4213/dm1547) · [Krapivin, Przybocki and Subercaseaux](https://doi.org/10.4230/LIPIcs.SAT.2026.23)

## Remainder in the matching construction

If the two incidence layers are counted separately and the tail computes threshold five on all w vertex signals, the resulting gate ledger has an Ω(n^(3/10)) remainder. This proves sharpness for the specified construction. The unrestricted lower bound above uses an additional structural argument. [Gate-count proof](matching-ledger-lower.md)
