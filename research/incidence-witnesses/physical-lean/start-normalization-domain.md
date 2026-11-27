# Start of the order-401 deletion schedule

`IncidenceStartNormalization.lean` uses actual code positions, input sets and an arbitrary output index. It counts both physical ports of a binary gate, even when the operands agree. Its two stage records concern the outputs of the hoists. The bounded-arity copy and zero gates of the original posted program must first be forwarded or propagated; these entries do not represent additional binary readers in either census. Make the program live before normalizing it. Retain the literal gate and reader counts in the simultaneous transformations. Charge any later dead pruning as its own physical operation.

| Experiment | Starting DAG and promise | Required result |
| --- | --- | --- |
| Line OR-spine hoist | Live binary baseline; arbitrary points and at most 401 selected lines | Same or smaller size; all positive flags and original one-sided sparse domain retained; every remaining once-read line first feeds an AND |
| Line census | That line-normalized DAG with below-target size | At most 3382 once-read line inputs |
| Point OR-spine hoist | That *same* line-normalized DAG | Same or smaller size; positive flags and negatives with at most 401 points and 400 lines; literal multiplicity of each line input retained; every once-read point and line enters an AND |
| Point census | Result of both hoists with below-target size | At most 6461 once-read point inputs |
| Actual first deletion | Result of both hoists, before either census's hypothetical marker edits | At most 9843 once-read inputs, all with AND readers; flags and independent three-by-three negatives survive |

For the first hoist take an independent test with no selected owner line x. Add a point of x avoiding the at most 401 active lines. This enlarged negative is still legal. Adding x can exceed the line promise, but the resulting mask dominates the incident singleton flag, so monotonicity forces acceptance. Globally hoisting a point spine on the full point domain fails in general; the second stage therefore uses its bounded two-shore domain.

The line census uses the full point mask outside each one- or two-line witness, and a common zero-query baseline. Its later-endpoint edit on each mutually chosen cold pair is an experiment: the physically charged OR/point weights and warm bypass savings belong to the original line-normalized DAG. The bound at h=52 applies if the number of charged owners is ≤1737; the h=53 bound applies if it is ≥161. At H≥3383 they cover all counts.

The point census uses witnesses of at most 199 lines avoiding up to two given points. In the two-by-two experiment a reciprocal bad partner can be erased using an earlier fork; the combined off-pencil test has at most 201 selected lines. In the ordinary warm case two witnesses and the two test lines require at most 400 selected lines. The chosen disjoint charged component slots give at most 3248 unedited owners, while the hypothetical weighted two-by-two intervention bounds the number edited by 3213. The point experiment does not need arbitrary point masks. Neither experiment supplies the retained circuit: substituting the experimentally edited circuits for the bilateral start would invalidate reader-count transfer.

The physical obligations are constructing both stage witnesses with these simultaneous guarantees and deriving both census bounds by their respective experiments. The current Lean interface proves how these witnesses yield the actual start and proves how the posted tests supply the input negative promise; it does not construct the witnesses. Geometry comes from the official plane hypotheses, including the derived dual properties. The paper's proof concerns under-target programs on exactly the order-401 plane.
