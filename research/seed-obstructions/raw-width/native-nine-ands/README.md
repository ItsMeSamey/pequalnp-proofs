# Dependencies among dirty gates in the nine-AND circuit

In a native nine-AND separator whose sole clean AND is the output, there are at least two distinct ordered dependencies between dirty AND gates. That count alone allowed both dependencies to start at one gate. The [stronger source theorem](native-nine-two-distinct-dirty-donors.zip) excludes that possibility. At least two distinct dirty AND gates must each feed another dirty AND. The [independent review](TWO-DONORS.md) permits arbitrary fanout and OR count. The [dependency proof and signed checks](native-nine-one-dependency-exclusion.zip) use no OR-count assumption.

The [override recurrence](native-nine-row-overrides.zip) follows a single forced gate value through all of its readers, including reconvergent paths. For the size-at-most-33 nine-AND case, an acyclic wire replacement that passes its positive and negative tests would remove an AND, contradicting the original eight-AND exclusion. The recurrence was checked on all 676 indexed rows of a seven-AND, 27-OR separator and on all 64 inputs of a separate reconvergence fixture.

The [independent source review](dependency-review.md) identifies the dependency archive and the exact PROOF.md member of the override archive. The nine- and ten-AND cases remain open on all four banks.
