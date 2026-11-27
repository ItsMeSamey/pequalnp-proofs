# An exact family on the one-or-two-hot promise

Take physical flags a,d,e and m≥1 further flags p₁,…,pₘ. Among the nonempty assignments of weight at most two, accept exactly singleton a, the pair ad, and assignments supported entirely on the p flags. The exact minimum number of binary AND/OR and unary NOT gates with unrestricted sharing is m+5, or two more than the number of physical inputs.

For the upper, form P as the OR of all p flags in m−1 gates. The output is

    NOT ( (e OR (d AND NOT(a))) OR (a AND P) ).

This costs six further gates. If e is set, the result is false. Otherwise a and P conflict; if d is set then a is required. The nonempty promise gives precisely the stated positive assignments.

For the lower, if m>1, pin the last p input to zero. This input is essential since it changes singleton a from accepted to rejected when added. In a normalized live circuit its earliest consumer folds, saving at least one gate, and the restricted function is the family at m−1. Repeating gives a circuit for the m=1 base with at least m−1 gates removed. The four-input unique-fork proof in one-fork-proof.md excludes five gates at this base. The upper and lower coincide for every m. Desk mask 4297 is the m=2 instance with a=0, p₁=1, p₂=2, d=3, e=4.
