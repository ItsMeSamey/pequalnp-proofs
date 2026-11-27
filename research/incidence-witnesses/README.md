# Projective-plane incidence circuits

At order 401, every scalar monotone circuit satisfying the original sparse promise uses at least **644,809 gates**, with arbitrary fanout. The target of 646,425 gates is 1,616 higher. [Proof that equality at 644,808 is impossible](strict-dense-signature.md)

For the original one-sided promise of arbitrary point masks and at most q selected lines, [producer-component extraction](anchored/README.md) and its [combined cost bound](anchored/pruned-cost.md) give s≥4N−O(q) and verify 100s≥Nq through order 396. Here N=q²+q+1. The proof uses stronger tests than correctness restricted to input weight two.

The local lowest-common-ancestor refinement in the [extraction proof](anchored/README.md) extends the verified interval through order 397. At that order it gives 627,678 gates against the 627,288 target.

[Weighted flow through ports](weighted-flow.md) yields s≥4N−1−⌊4N/(q+2)⌋ for the original one-sided promise. This establishes 100s≥Nq through q=399, with three gates to spare at 399. The same estimate falls short at 400.
