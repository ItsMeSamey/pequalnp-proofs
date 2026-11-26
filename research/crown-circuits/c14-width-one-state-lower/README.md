# Three exclusive receivers per state

Consider a live regular monotone fan-in-two threshold-two circuit on fourteen raw inputs, of size at most 34, with five AND gates. Assume the one-dirty normal form with exactly one dirty AND, exactly one signed clean continuation literal, and minimum hot-label count among the applicable minimum representatives. In the resulting three-state trace representation, each of the inactive, positive and negative panels has at least three distinct raw receivers whose nonempty deficit lies entirely in that panel. At least nine receivers are therefore state-exclusive.

Read one-dirty-width-one-state-minors.md first, width-one-twelve-grid.md second and width-one-active-three.md last. The first file states the trace and reverse-union budget of the normal form used in the proof. External prerequisites include the one-dirty trace reduction, the four-axis fourteen-receiver packing exclusion at 21 joins, and the established threshold size lower bounds C(11)≥27, C(12)≥29 and C(13)≥32. The argument is a source-level mathematical proof. It leaves the existence of circuits satisfying the resulting state counts open.

All three proof sources received independent exact-source review by the algebra desk. SHA256SUMS identifies the reviewed files and this cover.
