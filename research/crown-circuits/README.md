# False OR gates on a crown diagonal

The 12-crown has minimum size **41 among binary monotone circuits with at most five AND gates**, allowing unrestricted sharing. The five-AND proof combines mathematical reductions with executable checks covering 617 canonical profiles. Together with the kernel-checked lower bound of 32 OR gates, it leaves exactly six, seven or eight AND gates possible for a circuit of size at most 40. Whether such a circuit exists remains open. [Five-AND proof and replay](five-and-general-cert/README.md) · [32-OR kernel audit](kernel-or-count/README.md)


Every monotone binary circuit of size at most 40 representing the 12-crown on one-row, one-column inputs requires **at least 24 OR gates and at most 16 AND gates**. The kernel proof includes the threshold-two OR lower bound for physical circuits. The existence of a 40-gate circuit remains open. [Proof](twenty-four-ors.md) · [Lean theorems](../../lean/Research/CrownTwentyFourOrs.lean) · [Threshold-two lower bound](../../lean/Research/WegenerThreshold.lean)


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

Under the same joint size and OR budgets, at least 45 distinct wires feed OR gates and at least four of them are OR outputs. In the collision-free case these bounds rise to 46 and five. The number of AND gates plus the number of distinct OR outputs feeding OR gates is at least 21, or 22 when there is no collision. [Source-count theorems](../../lean/Research/CrownMandatoryOrSources.lean) · [Collision-free bounds](../../lean/Research/CrownFourOrSources.lean)

A [41-gate grid circuit](../../lean/Research/CrownGrid41Verified.lean) represents the 12-crown on all 144 promised inputs using five AND gates. This attains the [restricted lower bound](formula-banks/single-shared-bank-volume-proof.md) for arbitrary OR banks over the twelve paired signals, with at most one shared intermediate OR aggregate, followed by a binary monotone formula. Internal sharing in an unrestricted downstream circuit remains open at size 40. The restricted lower bound has an independently reviewed mathematical proof and three reproducible arithmetic checks.

Two concrete 29-gate repair prefixes have no binary monotone suffix with at most eleven gates, even with fanout. Their frozen wire sequences and verifiers are in [the first certificate](prefix-cert-seed1/PROOF.md) and [the second certificate](prefix-cert/PROOF.md). With only the seven grid aggregates as inputs, a suffix needs exactly twelve gates. [Grid suffix certificate](grid-seven-cert/PROOF.md)

In a size-at-most-40 representation with exactly 24 OR gates, at most six raw singleton inputs activate no OR gate. If there are six, all six belong to the same side of the crown. [Lean proof](../../lean/Research/CrownSixSameSide.lean)

The [full grid-prefix certificate](grid-full-cert/PROOF.md) lets the suffix read every raw input and every wire of the fixed 29-gate grid prefix, with arbitrary DAG sharing. No suffix of at most eleven binary monotone gates works. The 41-gate witness supplies a twelve-gate suffix, so twelve is exact for this prefix. The independent clean replay used the published source files and exhausted all source counts seven through twelve. [Replay log](grid-full-cert/independent-replay.log)

For every n ≥ 3 the n-crown requires exactly 3n−4 binary OR gates, even when AND gates are free and arbitrary sharing is allowed. Thus the 12-crown requires 32 OR gates. The [written induction](crown-or-cost.md) is independently reviewed. The [full kernel audit](kernel-or-count/README.md) covers the base case and the physical induction. This OR count alone leaves the unrestricted 40-gate total open.

A size-at-most-40 circuit for the 12-crown cannot have exactly four AND gates that all evaluate false on every diagonal input. The proof reduces the necessary reverse-wire masks to 279 packing classes, all excluded with a 17-union budget. Circuits with an AND gate active on a diagonal require a separate argument. [Derivation and replay instructions](four-clean-ands/fourand-clean-transpose.md)

The 12-crown requires **exactly 41 gates among all binary monotone circuits using at most four AND gates**. The rejection search allows arbitrary sharing and topology. The 130 rejection certificates passed DRAT verification, and the 41-gate upper witness was checked on all 144 inputs. [Four-AND model and replay](four-and-cert/four-and-model.md)

A separate proof gives exact size 41 for arbitrary raw OR-only preprocessing followed by terminal comparisons and OR aggregation, including shared OR gates and any number of comparisons. General circuits can also put diagonal-active ANDs in the prefix. [Raw-bank proof](arbitrary-raw-banks/arbitrary-raw-banks.md)

The [standalone Lean theorem](../../lean/Research/CrownShardStandalone.lean) gives a physical lower bound of 31 OR gates and an upper bound of nine AND gates at total size at most 40. Its axiom audit lists only propext, Classical.choice and Quot.sound. The stronger 32-OR bound above is independently established by the mathematical induction.

With five AND gates, size 40 is also excluded in the normalized case with exactly one diagonal-active AND and four clean terminal comparisons. The eight search strata cover 75,688,399 helper families. [Proof and census](five-ands-one-dirty/five-one-dirty-proof.md)

The full [standard-axiom Lean certificate](kernel-or-count/README.md) now verifies the general 3n−4 OR lower bound, the 32-OR bound at n=12 and the consequent cap of eight AND gates at total size 40. It includes the kernel-checked finite base case.

A 31-gate prefix can summarize nine labels by two wires. A suffix reading those two wires and the six raw ports of the remaining labels needs at least eight OR gates and two AND gates. The Lean audit lists the three standard axioms for both endpoints. [Folded-prefix proof](folded-kernel/folded-residual.md)

Unrestricted size at most 40 for the 12-crown is equivalent to size at most 28 for twelve-input threshold two. Both remain open. [Equivalence, finite prerequisite and replay](universal-pairing/README.md)

For the paired twelve-label model, a threshold-two tail with exactly six AND gates cannot fit within 28 binary gates. All six possible clean-terminal counts are covered. The finite proof uses the previous five-AND exclusion, clean-bank theorem, and direct-receiver normalization. The census lies outside the Lean kernel. The unrestricted 12-crown size question remains open. [Scope and replay](six-paired-cert/six-paired-scope.md) · [Five-AND dependency](five-and-general-cert/README.md) · [Unrestricted size transfer](universal-pairing/README.md)

A normalized paired seven-AND threshold tail of size at most 28 must have at least four diagonal-active AND gates. The three-active proof checks 36,396 chronological templates and uses the separate zero-, one- and two-active exclusions. Four or more remain open. [Three-active proof](paired-seven-ands/three-dirty-preliminary.md) · [Six-AND chronology clarification](six-paired-cert/chronology-clarification.md)

Unrestricted binary monotone threshold two has minimum size **19 on eight inputs and 21 on nine inputs**, on the full Boolean cube. Constructive upper bounds were checked on all 256 and 512 inputs. Independent searches agreed on the budgets and verdicts for 25,721 and 25,680 profiles respectively. Separate exact checks rejected the remaining 797 and six profiles. Splitting a threshold input and the explicit upper constructions also give exact sizes 4, 7, 10, 13 and 16 on three through seven inputs. These are mathematical and executable finite proofs. The twelve-input size-28 question remains open. [Eight-input proof](threshold-eight/eight-proof.md) · [Nine-input proof](threshold-nine/nine-proof.md)
