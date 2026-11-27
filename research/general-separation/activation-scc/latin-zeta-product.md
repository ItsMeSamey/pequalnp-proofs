# Exact clause products on a signed 2CNF boundary

Find a model a of the supplied 2CNF H or return NO. Set z=x xor a. Every normalized clause of H is an implication, a negative conflict or a negative unit. Supports F are exactly the implication-closed sets avoiding conflicts and negative units.

For each feasible closed set U let e_U(F) indicate containment of U in F. Their evaluation matrix on feasible sets ordered by size is unitriangular. A monomial on T is zero if its implication closure violates a negative requirement, otherwise it is e_cl(T). Multiplication of basis functions therefore normalizes the union, returning zero for infeasible unions.

Start with e_empty. For each physical width-three clause multiply its pass indicator, one plus the product of its false-literal indicators, into the dictionary over GF(2). Expand just that factor into at most nine terms, normalize each union and toggle its coefficient. All occurrences refer to the same actual signed-star coordinates. The dictionary is exactly the pointwise product on H models after every step. An empty dictionary certifies NO. After the last clause a smallest-cardinality retained U gives an actual model: evaluation at U is one because no smaller retained set lies inside it. Return x=a xor 1_U and replay the original clauses.

With polynomial-time implication closure and sorted dictionaries, time is polynomial in explicit input size times the sum of intermediate dictionary sizes. Space charges their maximum. An arbitrary binary join charges the product of its two input dictionary sizes before cancellation. This gives an unconditional decision and search algorithm on the full signed Latin target with an uncontrolled exponential parameter.

Even for m disjoint positive ternary clauses with empty H, the final dictionary has at least 2^m terms under every baseline and every order. Each local translated pass indicator has seven models out of eight, whereas a single monomial has a power of two. Thus every factor has at least two distinct terms. Their variable sets are disjoint, so products of distinct choices do not cancel. This is an explicit representation-size result on an easily satisfiable family.

This combines the activation team's degree-bounded actual-model basis with ordinary implication closure and the zeta basis of a finite poset.
