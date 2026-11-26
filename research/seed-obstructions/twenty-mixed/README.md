# Exactly twenty mixed gates

A size-33 residual separator with twenty mixed gates and eleven point boundary wires cannot have seven line boundary wires. The connected cone then has three surplus operand uses. Counting its singleton-resident regions and accounting for the remaining point leaves gives at least fourteen pure point gates. This excludes all placements in this cell. [Proof by cases](seven-lines.md)

The [two-arm](two-arms/README.md) and [three-arm](three-arms/README.md) checks use the pinned samples. The [five-feature certificate](five-features/README.md) regenerates the 21 SAT instances and optional DRAT proofs. The standalone [three-special-role certificate](special3_certificate.zip) and [promoted-role certificate](zeroarm_certificate.zip) include the input and earlier point-projection dependencies. An independent reviewer checked the case coverage, the five-star equality argument and the completed DRAT verification logs. The individual checks can be replayed separately.

For width twelve, the read-once case with nine distinct line signatures has a separate [point and line cost analysis](../four-private-twelve/read-once-nine.md). The [point-cost certificates for widths 13 through 17](diagonal_fourgroups.zip) extend the four-private-group lower bounds. The existence of a 33-gate residual separator remains open.

For every point width, a read-once mixed tree with nine line leaf occurrences needs at least 34 gates. This includes repeated and null line signatures. Reviewers regenerated the cost-six split cases and all 25 quartet searches for widths 13–17, and checked the occurrence counts in the earlier seven- and eight-line reductions. [Proof](nine-readonce.md)

## All twenty-mixed cases

Every residual separator of size at most 33 must use **at least 21 mixed gates** and at least eleven point-boundary signals. The three remaining eleven-point cases close as follows.

- With eight line inputs, the [pair-support certificate](pair-support-certificate.zip) checks the final twelve surviving packets. The [three-line support](eight-two-s3.zip) and [remaining support cases](eight-two-certificate.zip) complete the allocation.
- With ten line inputs, the [point-cost analysis](ten-line-point-cost.zip) and [matched normalization](ten-line.zip) exclude the 105 remaining disjoint-pair configurations.
- With nine line inputs, the [last-case proof](nine-lines.md) uses the [star-local frontier](star-eleven.zip), [zero-resident](zero-resident.zip) and [promoted-role](e1_five_cert.zip) reductions. The [two-star audit](two-star-cut.zip) independently enumerates all 660 tight raw-source profiles. Matching their remaining ten raw operand slots leaves no nonlocal bank satisfying all 1,323 obligations. The [independent equality-forest search](equality-forests-final.zip) reaches the same conclusion.

These proofs use the earlier point-cost and gate-count results. The raw-operand argument requires rejection of the full negative samples by an actual separator. The certificates have separate replay procedures. The general 33-gate feasibility question remains open.
