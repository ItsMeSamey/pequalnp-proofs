# Higher mixed budgets with ten point boundary signals

This checker continues the 17-mixed proof using its original formal statement and the same four point-family inputs. For each family, the original pure point cost, the number of mixed gates, and the number of paid pure line gates must sum to at most 33.

For a ten-mask extension of a nine-mask base, recompute every target's pair-safe reconstruction cost from the raw point/line rows. An input signal that alone distinguishes a positive/negative pair, with the positive line vector dominated by the negative line vector, must reject the negative's point vector. It therefore rejects all point pairs therein. For each target, let c be the minimum number of these verified pair-safe target submasks and raw target singletons covering the target. The corresponding reconstruction needs c−1 extra OR gates and supplies a pair-safe complete target. Write b=21−Σ(c−1).

For each tested original point budget K, apply the preceding augmentation theorem's geometric bound with slack d=K−b. At d≤2 it gives no two-charge exceptional target and at most d exterior gates. The original point circuit consequently owes at least 4−c charges for each target. The existing target-local subset dynamic program, exterior-input enumeration and disjoint gates needed for required transverse masks apply unchanged with K replacing 16. The code skips this test for d>2, grants the empty mask free, and charges repeated required masks only once. Over the 27,786 distinct nine-base extensions passing the 17-mixed augmentation verifier, 1,365 retain budget 15 and 26,421 first pass at 16. No extension retains budget 14. The separate six-target bound deals with supersets of a base having at most eight point signatures, exactly as in the 17-mixed proof.

The 23,274 irreducible families have point lower bounds from 12 through 16. For a mixed budget m≥18, at most 33−m−12≤3 pure line gates are affordable. The checker enumerates their singleton signatures by extending the seven raw line bits with AND/OR and choosing all boundary multisets of the requested size. If the positive point vector in a positive/negative pair is dominated by the negative point vector, at least one line input must distinguish it. Applying this test gives 29, 64, and 99 possible eight-line multisets with one, two and three paid gates. For nine-line multisets the counts with two and three paid gates are 540 and 2,069. At exactly seven line signals we use their forced seven singleton signatures; lowering each to its raw line bit preserves positives and only decreases negatives. At least ten line signals would need at least three paid line gates, which leaves no connected mixed graph at these point and total budgets.

As in the preceding proof, the point and line functions can be replaced by the ORs of their singleton signatures. The checker verifies the 24 simultaneous point/line permutations against the decoded 28 positive and 245 maximal negative raw rows before taking orbits. The received line signals are permuted together with the point masks. The C++ search represents frontier multisets, retains neither, one or both selected operands, and charges each retained operand against the exact surplus m−(10+L−1). It includes higher fanout at a single signal, including a boundary signal. It omits a same-wire idempotent mixed gate, which can be deleted in a minimum circuit; in particular, exclusions at smaller mixed budgets already cover its simplified graph.

The elementary private-pair pruning from the 17-mixed checker applies at every frontier. The additional necessary graph-coloring test is proved in fanouts.md. Where the last extra use retains one existing operand, every conflict edge must touch that operand, because all other frontier variables have independent, single occurrences in the rest of the formula. Where the last two extra uses retain both existing operands, every conflict edge must touch one of them. When the full-surplus state set grows large the checker can discard states failing the read-once conflict condition. This is an exact rejection criterion. There is no time or search-size cutoff in the release checker.

Run with Python 3 and C++20. For example, the following checks the nine-line case at 19 mixed gates. Changing the two flags selects another row. The path arguments match those of the default 17-mixed checker.

```sh
python verify.py --mixed 19 --lines 9 L-meta-18968.json refined-all.txt nine.txt geom_survivors.txt dupgeom_survivors.txt
```

A surviving mixed frontier or missing result fails the checker. With 22 or more mixed gates, the lower bound of 12 point gates already exceeds the total limit of 33. This argument concerns ten point boundary signals.

After running the [17-mixed driver](../seventeen-mixed/README.md) with output directory `/tmp/seventeen-check`, reproduce a complete mixed-budget row from this directory with the following command. Replace 18 with 19 or 20 for the other completed budgets.

```sh
python3 verify.py --mixed 18 ../L-meta-18968.json /tmp/seventeen-check/ten/refined.txt ../nine-signatures/nine.txt /tmp/seventeen-check/distinct-survivors.txt /tmp/seventeen-check/duplicate-survivors.txt
```
