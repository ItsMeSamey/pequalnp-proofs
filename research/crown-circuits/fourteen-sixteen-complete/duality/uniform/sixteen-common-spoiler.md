# One external singleton can spoil all three path flags

Let x,y be independent labels on a P3, with flags x,y and g=x∨y. Take three further independent labels z,w,t. Set X=x∨w, Y=y∨w, G=g∨t and B=X∨Y. The decoder

    (X∧Y∧G) ∨ [z∧(B∨G)] ∨ (t∧B)

computes threshold two on x,y,z,w,t. With no external label the result is xy. With z alone present, adding either local leaf, the center, or either other external raw makes the second disjunct true. With w present the first disjunct accepts either local label; with t present the third does so. The pair w,t also accepts. Zero and all singletons reject. Checking all 32 independent input assignments agrees. All three P3 flags have separate single OR readers, yet z alone spoils each individually. This costs seven ORs and four ANDs in the decoder. It is a local realizability test and does not supply a q16 decoder at the global cap.

A smaller AND-center variation uses just z,w externally. With X=x∨w, Y=y∨w, W=(X∧Y)∨z, the output (g∧W)∨[z∧(X∨Y)] computes threshold two on x,y,z,w and z spoils each formal flag. Its W is private, so this example does not have the physical shared-partner property of the minimum q16 residual.

## Sharing before the merger

Suppose a negative external singleton z spoils both ordinary leaf flags individually. With the center fixed true and all external flags zero, the function of the two leaves is AND. Both true is a positive local pair, exactly one true gives a negative actual singleton, and neither true rejects by monotonicity. With the center false and the external singleton z present, the function of the same two leaf flags is OR. Under either setting both leaves are essential.

Follow the two leaf wires until their paths first branch or meet. If their paths meet before either can branch, there is a first combining gate. Until that gate each arm is a unary monotone function of its own leaf once the other source flags have been fixed. Essentiality forces both unary functions to be identity. All subsequent leaf dependence passes through the combining gate, and the downstream unary function must also be identity. Therefore its physical type would need to be both AND and OR. This proves that at least one leaf channel must encounter a fanout before merging with the other (a fork at the combining gate itself is too late).

If z spoils all three flags and the formal local leaves together without their center still reject, the local function on x,y,g is AND3 and at z it is OR3. Every unordered pair of the three variables switches between AND2 and OR2 upon holding the remaining variable at one or zero respectively. At least two distinct first-fork gates are necessary: no two not-yet-forked channels can meet even at their first joint fork, by the two-variable argument. At most one channel can reach the output without a fork. If the centerless local pair accepts, the pure local function is instead xy independent of g, and only the two-leaf conclusion follows. Distinct P3 components may share resources, so no additive lower bound across components is asserted.
