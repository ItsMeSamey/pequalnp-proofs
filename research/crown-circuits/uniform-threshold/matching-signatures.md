# A two-stage matching construction

For all sufficiently large n there is a fan-in-two monotone circuit for threshold two with at most 2n+√(2n)+O(n^(3/10)) gates.

Take m=ceil(√(2n)+K(2n)^(3/10)) and w=ceil(m^(3/5)), with K a sufficiently large fixed constant. Choose m distinct edges uniformly from the complete simple graph on w vertices. There are binom(m,2) unordered pairs of these edges. Discard intersecting pairs. Among the remaining pairs, retain one matching per distinct four-element endpoint set.

The expected number of intersecting pairs is at most O(m²/w), by conditioning on the first edge. The number of discarded duplicate matchings is at most the number of unordered pairs of distinct matchings on the same four-element set. Their union is a 4-cycle, and each 4-cycle gives exactly one such pair, irrespective of other edges. The expected number of these cycles is at most 3 binom(w,4) (m/binom(w,2))^4, by sampling without replacement. Thus some graph loses O(m²/w+m⁴/w⁴)=O(m^(8/5)) pairs. The surplus binom(m,2)−n is at least K(2n)^(4/5)−O(√n); fix K larger than the uniform constant in the loss bound. At least n four-element signatures survive. Choose n of them, associating each with its one retained matching.

For each used graph edge b, compute the OR of all input labels whose matching contains b. If m' graph edges are used, this layer costs exactly 2n−m'. On each incident graph vertex take the OR of these edge signals. If w' vertices are used, this costs 2m'−w'. Apply threshold five to those w' signals. A single label activates four vertices, and two different labels activate at least five. For fixed threshold five the standard prefix recurrence tracking thresholds one through five uses at most 9w' gates. The circuit costs at most 2n+m'+8w'≤2n+m+8w.

This is an unrestricted upper bound from an explicit finite selection rule (one can search for a suitable graph). Its exponent 3/10 is below the 1/3 term of separate multipartite modules in SAT 2026 Appendix A.2. The argument neither lower-bounds other architectures nor establishes a sharp third-order exponent.
