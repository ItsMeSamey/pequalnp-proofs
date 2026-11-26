# False OR gates on a crown diagonal

For a false cell in a one-hot input matrix, its row and column degrees sum to at most one plus the number of OR gates false on that cell. On the 12-crown, each diagonal cell therefore makes at least 21 OR gates false. If a circuit has 22 OR gates, each diagonal can make at most one of them true. The three formal modules are [ZeroCellDegree](../../lean/Research/ZeroCellDegree.lean), [FalseOrCount](../../lean/Research/FalseOrCount.lean) and [TrueOrCount](../../lean/Research/TrueOrCount.lean).

Under the one-true-OR hypothesis, the [diagonal marker argument](one-active-or.md) gives a lower bound of 33 AND gates for the 12-crown. This step is a paper proof. To reproduce the finite checks, run the following commands in this directory.

```sh
g++ -std=c++20 -O2 one-active-check.cpp -o /tmp/crown-one-active
/tmp/crown-one-active
```

[CrownGateCounts](../../lean/Research/CrownGateCounts.lean) formally proves that representing the 12-crown with at most 21 OR gates needs at least 132 AND gates. Every representation of total size at most 40 therefore has at least 22 OR gates.
