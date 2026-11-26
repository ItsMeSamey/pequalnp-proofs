# Gate elimination for the incidence promise

The [completed verification](../lean/Research/AdaptiveIncidence.lean) now establishes the deletion bounds and the target inequality through order 288. The derivation below records how the intermediate conditional estimates fit together.

## Restriction preserves the tests

Let G be the incidence graph, with N = q²+q+1 vertices in each part. Every line has q+1 points. For each point p, the sets of other points on the lines through p partition the N−1 other points, with q in each set. Therefore exactly q+1 lines pass through p. Two distinct same-side vertices have at most one common neighbor. For line vertices this follows by applying uniqueness of the line through two distinct common points.

Every assignment with at most q selected line coordinates has output equal to the incidence edge predicate. An incident pair is an accepted lower assignment. If there is no such pair, the input is below the specified rejected assignment for its line mask. All gate operations are monotone. Thus setting any set D of variables to zero preserves this equality on sparse assignments of the induced graph. In particular, for q ≥ 2 the circuit is correct on all zero-, one-, and two-bit assignments throughout.

## One deterministic elimination step

Use a topologically numbered circuit for the current output. Drop gates that do not feed the output. Bypass copies, identical-argument gates and gates whose value simplifies against a constant, forwarding the appropriate earlier signal (or constant zero) to all their uses. The circuit size counts gates, so these changes can only decrease it. If the output is a remaining genuine gate, the lowest one has two distinct input variables a and b as parents.

If a parent occurs in at least two distinct remaining gates, set that variable to zero. Each occurrence independently simplifies its gate. An AND becomes constant zero and an OR becomes its other parent. Process occurrences in topological order and forward every simplified output. A later occurrence may already have disappeared because its gate became dead or constant. It still counts as a distinct removed gate. The resulting restricted circuit costs at least two fewer gates. In a tie, delete the smaller-index eligible variable.

Otherwise both parents occur exclusively in this one gate. Transposing them preserves its output and consequently the final output on every assignment. A transposition distinguishing the graph's two-element edge sets would contradict correctness on those assignments. For two vertices on the same side, transposition invariance implies equal neighborhoods. They have at most one common neighbor, so both degrees are at most one. For vertices in opposite parts, an edge from either parent to a third vertex would transpose to a nonedge in a single part. Again both degrees are at most one. Delete the smaller-index of the two parents. The restricted circuit loses at least its lowest gate.

Every nonisolated vertex is an essential input. An incident two-bit assignment is accepted and switching off that vertex gives a rejected singleton. With at least one edge remaining the output is neither a constant nor a lone input, since the empty assignment and every singleton are rejected. Thus a lowest gate is available whenever the induced graph contains an edge.

## The additive q bound

Perform q successive variable deletions. Before each deletion all remaining vertices have degree at least two. The low-degree exceptional case of the elimination step can never occur. After the last deletion every remaining degree is at least one. Same-side vertices still have different neighborhoods, because their original neighborhoods differ in at least 2q coordinates. Opposite-side vertices cannot both be adjacent only to one another, because that would require at least 2q deletions in two disjoint parts. Hence every transposition is distinguishable at this stage. Apply the generic first-gate argument in FirstGate.lean to the 2N−q remaining essential inputs. The resulting paper bound is 2q+(2N−q) = 2N+q gates.

## A linear excess from packing

Set d = (N−3)/2 and perform d deletions. N is odd. For any prefix with deleted set D of size at most d, define B(D) as the set of original vertices with at most one neighbor outside D, including vertices already deleted. Each part contains fewer than q vertices of B(D). Indeed q of them would each have at least q neighbors in D, and their neighbor sets intersect pairwise in at most one element. Their union would contain at least q²−q(q−1)/2 = (N−1)/2 elements, more than D. The checked lemma DeletionPacking.few_depleted gives this inequality from the finite-set hypotheses.

There are still original vertices outside D and B(D), since 2N−d > 2(q−1) for q ≥ 2. Such a remaining vertex has at least two remaining neighbors. Consequently every requested step has an edge and can be performed. A step costing only one gate deletes a vertex already in B(D) for its prefix. This set grows with D, so the number t of these deletions plus the number z of isolated remaining vertices satisfies t+z ≤ 2(q−1) at the end. The two groups of vertices are disjoint.

The steps delete at least 2d−t gates. The residual circuit depends on at least 2N−d−z variables, so it contains at least 2N−d−z−1 gates, by the binary fan-in support bound. Adding yields at least

    2N + d − 1 − 2(q−1) = (5N−1)/2 − 2q.

This is still linear in N. In particular the argument does not yield the Nq/100 lower bound at all orders.

## Using the second moment of the neighborhood sizes

For one part, let t count the depleted vertices and let d₁ be the number of deleted vertices in the opposite part. Each depleted vertex has at least q and at most q+1 neighbors among those deletions. Two vertices share at most one neighbor. If cᵢ is the number of these neighborhoods containing deleted vertex i, then Σcᵢ ≥ qt and Σcᵢ² ≤ t(q+1)+t(t−1). Cauchy–Schwarz gives q²t² ≤ d₁t(q+t). Lean checks this in [IncidenceMoments](../lean/Research/IncidenceMoments.lean).

Apply this to both parts. For total deletions d < q² and total depleted count b, the result gives b ≤ ⌊dq/(q²−d)⌋. If a deletion sequence achieves the stated savings and support bound, the original gate count s then satisfies 2N+d ≤ s+1+⌊dq/(q²−d)⌋. Taking d=q²−17q proves the target inequality throughout 201 ≤ q ≤ 288 **conditional on the deletion sequence**. [DeletionThreshold](../lean/Research/DeletionThreshold.lean) checks both the combination and the finite arithmetic. The end-to-end verification above discharges the deletion-sequence condition.

The [restriction compiler](../lean/Research/CircuitRewire.lean) now checks a single rewiring step, its circuit semantics, and the cost of the gates directly consuming a removed input. The adaptive iteration composes this compiler with the graph-based choice of inputs.
