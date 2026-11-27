# Average exceptions under the uniform witness distribution

Let A be a nonempty subset of m-bit strings and δ=|A|/2^m. For each w∈A write u(w) for the number of prefixes along its path having exactly one viable child, and e(w) for the number of those prefixes whose child subtree is not full. Then

    E_uniform(A) 2^u(w) = 1/δ,
    1/(2δ) ≤ E_uniform(A) 2^e(w) ≤ 1/δ.

Generate a viable path by choosing equally when both children are viable and taking the sole child otherwise. Each leaf w has probability 2^(u(w)−m); summing gives the identity. A nonexceptional unary node enters a full subtree, so at most one unary node per path is nonexceptional. The inequality follows. Applied inside any viable subtree, the identity recovers the inverse conditional witness density. The [half-density theorem](hereditary-witness-density.md) imposes the hypothesis at every viable prefix.

For B>1 let a proposed list H have size ≤(1−1/B)2^m. Its complement is nonempty, avoids H and has E 2^e≤B (indeed E 2^u≤B). Thus every universal list for positive families obeying only this root moment bound needs more than (1−1/B)2^m strings. The bound holds also for length-dependent B>1. For polynomial-size H the avoiding family has E 2^e≤1+o(1), so even the fraction of witnesses with any exception is o(1). Complements of explicitly generated lists have efficient membership by direct comparison. At B=1 for e, every witness is exception-free and the optimal universal hitting size is m+1 by the [pathwise theorem](hereditary-prefix-exceptions.md). For u, B=1 forces the full cube.

This excludes a common small test list under bounded mean or bounded exponential moment, even when almost all witnesses are exception-free. It gives no lower bound for solvers using the verifier description.
