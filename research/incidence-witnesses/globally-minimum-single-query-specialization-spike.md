# An unbounded single-gate singleton-query specialization count in an exact minimum

Use arbitrary point masks, empty queries permitted, and any positive cap on the number of query labels. The count T_g is as in single-query-semantic-library-audit.md: initialize the dictionary with constants and individual point raws, and record all new distinct point functions at gate g under singleton-query specializations, processing original gates in topological order.

## Three-gate reduction for a query with a private leaf

Let y have a private point neighbor r of degree one and another point neighbor p. Start with a trimmed gate minimum, constants propagated. If y has only one read and initially feeds OR, follow its maximal unbranched OR spine, stopping at a shared exit or just before a sole AND reader. It cannot end at the output, since pure y must reject. The exit is y OR its off-spine siblings; no sibling depends on y, since the spine below its exit has only one outgoing path.

Every sibling is zero on every legal independent mask. Otherwise remove y (which does not affect that sibling) and then add r. This mask is still legal and independent since r is incident only to y. Adding y now leaves the exit high and every other boundary input unchanged. But the resulting mask dominates the genuine flag r,y and must fire by monotonicity, even when the final addition exceeds the cap. Contradiction.

Replace that whole spine by y at its old exit and append the OR of every old off-spine sibling to the scalar output, using at most one OR per removed spine OR. This is correct: the core only decreases on negatives, and all the added siblings reject them. A lost positive would require y zero and a true old sibling, whose computation is unchanged because the spine had no escape below its exit and a path from the exit back to a sibling would be a cycle. Thus all flags persist. This gives a circuit no larger; any trimming discount would contradict minimum size. It has y multi-use or directly entering a sole AND.

Fix y,r to zero, leaving a nonzero residual. The raw outgoing slot total U for these two variables is at least three if y is multi-use. In general the number of gates with a forced-zero parent is
U plus the sum of (fanout−1) over forced-zero internal signals plus the number of ANDs with exactly one forced-zero parent. To check this evaluate the others at all ones, and at each gate count its zero operands minus its zero-output indicator, adding one for an AND with just one zero operand. This gives one exactly at gates with a zero parent. The internal sum is nonnegative because the circuit is trimmed and the output stays nonzero. All counted gates are removable by constant folding. If y is sole-use at y AND B, B is independent of y and must accept the surviving raw singleton p: otherwise adding y to p would not change the scalar. Thus this AND contributes the needed third gate above the two raw slots, even when r is also sole-use. At least three gates can always be removed.

## Connected plane-induced example

Let z be incident to y₀,y₁,…,y_n and let p_i have only the neighbor y_i for 1≤i≤n. These edges are induced by a pencil through z and one noncentral point on each non-base member of a projective-plane pencil. The exact unrestricted gate minimum on the stated promise is 3n+1. Delete p_i,y_i at a three-gate discount, iterating on a fresh gate minimum at each step; the last edge z,y₀ costs one. The matching upper is

    [z AND OR(y₀,…,y_n)] OR [OR_i (p_i AND y_i)].

At its last OR, the n specializations at y_i are distinct z OR p_i. None occurred earlier: all left-side specializations are constants or z, and all matching subtree specializations are constants or a lone p_i. Thus the exact minimum has |T_root|=n, including n=26 at size 79. It lives as an induced subinstance in order 27, for example. This is not a minimum-size assertion about the entire plane.

## Degree-two alternative

Use n disjoint paths with edges p_i x_i, p_i y_i, r_i y_i. Delete r_i,y_i for every i by the preceding bound, retaining n independent edges p_i x_i. These need at least 2n−1 gates, since the scalar depends on all 2n raws and its binary output cone is connected. The exact minimum is therefore 5n−1, attained by ORing the n terms p_i AND (x_i OR y_i) into one subtree, all n terms r_i AND y_i into another, and joining by a final OR. This last gate again specializes at y_i to n distinct p_i OR r_i, absent earlier. At n=26 the degree-two graph already gives 26 functions in a 129-gate exact minimum with a query cap as small as one. Under constant disjoint path decompositions the same minimum permits other collector orderings. The example refutes a universal per-gate pointwise bound, not a claim that every minimum has a spike or that the average across gates exceeds 25.

## Full-plane scope

In the ordinary minimum-size point-star formula on a full plane, append the last point owner p to a left-comb collector as its final OR. Every one of the q+1 incident queries creates its full point star as a new function there: the earlier collector lacks p, and the last owner term specializes only to p or zero. Other queries add no new function. Thus |T_root|=q+1, exceeding 25 at q≥25. This formula's unrestricted DAG minimum status is unproved. On the full planes q≤4 no gate can have more than 25 such functions, because the number of query labels is at most 21.
