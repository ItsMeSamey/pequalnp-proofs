# Physical threshold-two regularity or a smaller circuit

For every binary monotone circuit C computing ordinary threshold two on n≥3 inputs, Lean proves at least one of the following.

- A binary monotone circuit computes threshold two on n−1 inputs using at most C.size−3 gates.
- An eligible lexicographically minimal representative computes the original function using at most C.size gates. In its decoded layout each raw input has exactly two distinct reader rows, both OR gates, and every gate has distinct operands.

The size comparison is to the supplied circuit. The smaller circuit can come from the minimizing representative. Gate-kind counts of the original circuit are outside the statement.

Lean 4.36 compiled `T2RegularOrDelete.regular_or_delete`. The final compiler receipt lists propext, Classical.choice and Quot.sound. The compiled object had SHA-256 `4438a57311abe834b6ef3e11c3dce6463daa3b1d2540732250b721aadfa6aa5d`. The source manifest lists local imports before their users. The sharp all-arity asymptotic bound remains a mathematical proof.
