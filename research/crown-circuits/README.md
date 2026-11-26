# False OR gates on a crown diagonal

For a false cell in a one-hot input matrix, its row and column degrees sum to at most one plus the number of OR gates false on that cell. On the 12-crown, each diagonal cell therefore makes at least 21 OR gates false. If a circuit has 22 OR gates, each diagonal can make at most one of them true. The three formal modules are [ZeroCellDegree](../../lean/Research/ZeroCellDegree.lean), [FalseOrCount](../../lean/Research/FalseOrCount.lean) and [TrueOrCount](../../lean/Research/TrueOrCount.lean).

Under the one-true-OR hypothesis, the [diagonal marker argument](one-active-or.md) gives a lower bound of 33 AND gates for the 12-crown. The [Lean marker proof](../../lean/Research/CrownMarkerBound.lean) now formalizes this argument and proves that any representation of total size at most 40 needs at least 23 OR gates. To reproduce the finite checks, run the following commands in this directory.

```sh
g++ -std=c++20 -O2 one-active-check.cpp -o /tmp/crown-one-active
/tmp/crown-one-active
```

[CrownGateCounts](../../lean/Research/CrownGateCounts.lean) formally proves that representing the 12-crown with at most 21 OR gates needs at least 132 AND gates. Every representation of total size at most 40 therefore has at least 22 OR gates.

[Weighted covers](../../lean/Research/CrownWeightedCover.lean) and [paired OR-tree depth allowances](../../lean/Research/CrownKraftCover.lean) give a 33-rectangle lower bound for the 12-crown under the stated depth hypothesis. The [two-active-OR construction](../../lean/Research/CrownTwoActiveRectangle.lean) exhibits a seven-gate circuit containing a sixteen-cell off-diagonal rectangle. [Punctured Fano covers](../../lean/Research/PuncturedFanoCover.lean) have a unique minimum cover, with a [cyclic graph generalization](../../lean/Research/CyclicCover.lean).

[Crown saturation](../../lean/Research/CrownFalseOrSaturation.lean) and [predecessor conflicts](../../lean/Research/CrownFalseOrConflicts.lean) describe any 12-crown circuit with at most 23 OR gates on a diagonal where two OR gates are true. Every false OR participates in the false cone, and the relevant predecessor sets are pairwise disjoint.

For any size-40-or-smaller 12-crown circuit, [the subcrown theorem](../../lean/Research/CrownSubcrownMarkers.lean) forces at least four diagonals where two or more OR gates are true. If the circuit uses at most 23 OR gates, [the wiring theorem](../../lean/Research/CrownOrWiring.lean) gives 21 OR gates with pairwise disjoint two-element predecessor sets.

[Uniform diagonal signatures](../../lean/Research/CrownUniformTrace.lean) give a k(k−1) AND bound for a k-element subalphabet when k≥3. A signature class in a size-40-or-smaller 12-crown circuit therefore contains at most four labels.

[Baseline normalization](../../lean/Research/CrownZeroOrNormalize.lean) and [distinct saturation](../../lean/Research/CrownDistinctSaturation.lean) require at least two different two-active-OR signatures under the size-40 and 23-OR hypotheses.

Under the 40-gate and 23-OR budgets, two distinct chronological pairs of OR gates each cover every predecessor overlap. The companion finite lemmas bound collisions of signed read sets and classify a four-vertex path under their stated hypotheses. All three modules pass the pinned Lean checker. [Indexed gate pairs](../../lean/Research/CrownIndexedOrReads.lean) · [Collision count](../../lean/Research/CrownSaturatedCollisions.lean) · [Path lemma](../../lean/Research/CrownCollisionPath.lean)

For the same budget the actual chronological OR-overlap graph has at most three edges and contains no four-vertex path. [Concrete collision theorem](../../lean/Research/CrownCollisionLimit.lean)

If there are three distinct overlaps, those three edges form a triangle. [Triangle classification](../../lean/Research/CrownCollisionTriangle.lean)

The earliest active OR gate on each positive diagonal admits an injective choice of an actual true input predecessor under these budgets. The masked-wire theorem transfers the chosen predecessors to the original circuit. [Earliest trigger](../../lean/Research/CrownFirstTrigger.lean) · [Masked-wire rigidity](../../lean/Research/CrownMaskedRigidity.lean)

Among distinct chronological OR gates, at most one unordered pair can share a valid predecessor in a 12-crown circuit with at most 40 gates and 23 ORs. [Unique collision theorem](../../lean/Research/CrownCollisionUnique.lean)

When there is a collision, four or five diagonals attain saturation. A wire feeding an OR is true on at most two diagonals, which share their OR signature. [Single-collision saturation](../../lean/Research/CrownCollisionSaturationFive.lean) · [Parent signatures](../../lean/Research/CrownParentSignature.lean)

If a single OR is the first active OR on two diagonals, exactly those two diagonals activate it. [Double-first theorem](../../lean/Research/CrownDoubleFirst.lean)
