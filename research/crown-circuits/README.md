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
