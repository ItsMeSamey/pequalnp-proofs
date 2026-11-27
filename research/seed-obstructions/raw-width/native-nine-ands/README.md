# Dependencies among dirty gates in the nine-AND circuit

In a native nine-AND separator whose sole clean AND is the output, there are at least two distinct ordered dependencies between dirty AND gates. That count alone allowed both dependencies to start at one gate. The [stronger source theorem](native-nine-two-distinct-dirty-donors.zip) excludes that possibility. At least two distinct dirty AND gates must each feed another dirty AND. The [independent review](TWO-DONORS.md) permits arbitrary fanout and OR count. The [dependency proof and signed checks](native-nine-one-dependency-exclusion.zip) use no OR-count assumption.

The [override recurrence](native-nine-row-overrides.zip) follows a single forced gate value through all of its readers, including reconvergent paths. For the size-at-most-33 nine-AND case, an acyclic wire replacement that passes its positive and negative tests would remove an AND, contradicting the original eight-AND exclusion. The recurrence was checked on all 676 indexed rows of a seven-AND, 27-OR separator and on all 64 inputs of a separate reconvergence fixture.

The [independent source review](dependency-review.md) identifies the dependency archive and the exact PROOF.md member of the override archive. The nine- and ten-AND cases remain open on all four banks.

### Disjoint input cones of sizes seven and one

For each original native bank, consider nine AND gates, eight dirty gates and one clean output. If the dirty ancestors of the two output operands form disjoint sets of sizes seven and one, no circuit fits the required rows, at any OR budget. The proof uses 194 families of indexed negative rows. An independent reconstruction recovered 101 minimal covers and 5,151 unordered pairs. Disjoint cones of sizes eight and zero, and cones with shared ancestors, remain open. [Proof](nine-disjoint-seven-one-exclusion.zip) · [Original-row control](nine-seven-one-independent-native-control.zip) · [Independent review](SEVEN-ONE.md)

### Simultaneous deletion and the twenty remaining incidences

The [Lean deletion theorem](../native-or-floor/native-paired-kernel-frozen.zip) keeps both gate counts on the same restricted circuit. A positive AND refund requires a witnessed AND gate hit by zero. This permits a conditional application to four single-read raw heads and exactly four private-reachable ANDs. After removing four specified incidences, covering all twenty remaining incidences with the exterior circuit requires at least six AND gates and sixteen OR gates. The archive includes the producer proof, the independent original-row comparison and the review of all 280 protected steps. [Residual-twenty proof and review](residual-twenty-review.zip)
