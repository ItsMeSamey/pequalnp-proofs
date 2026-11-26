# Threshold two at every arity

The matching construction gives **C(n) ≤ 2n + √(2n) + O(n^(3/10))**. Together with the lower bound below, this gives **C(n) = 2n + √(2n) + O(n^(3/10))**. The proof counts matching signatures and gives a deterministic finite search for a suitable graph. The optimal remainder is open. [Construction](matching-signatures.md)

For n ≥ 4, the minimum number C(n) of fan-in-two monotone AND/OR gates with unrestricted fanout satisfies **C(n) ≥ 2n + (√(8n−7)−7)/2**. The frozen manuscript received independent mathematical proof reviews. Combined with Theorem 9 of Krapivin, Przybocki and Subercaseaux, this gives **C(n) = 2n + √(2n) + O(n^(1/3))**. The full proof is a mathematical manuscript. [Proof of the stronger bound](shared-or-cut.md) · [Upper bound](https://doi.org/10.4230/LIPIcs.SAT.2026.23)

## Earlier all-arity bound

For every integer n ≥ 2, a binary monotone circuit for threshold two requires at least 2n + (4/3)√(n+3) − 6 gates. Four independent mathematical reviews checked the manuscript, including the component accounting, the star restriction and the induction. [Proof](threshold-lower.md)

Sergeev's lower bound is 2n + √((2n−4)/3) − 19/6. The coefficient of √n in the lower bound increases from √(2/3) to 4/3. Theorem 9 of Krapivin, Przybocki and Subercaseaux gives an upper bound of 2n + √(2n) + O(n^(1/3)). [Sergeev](https://doi.org/10.4213/dm1547) · [Krapivin, Przybocki and Subercaseaux](https://doi.org/10.4230/LIPIcs.SAT.2026.23)
