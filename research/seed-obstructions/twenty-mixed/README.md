# Exactly twenty mixed gates

A size-33 residual separator with twenty mixed gates and eleven point boundary wires cannot have seven line boundary wires. The connected cone then has three surplus operand uses. Counting its singleton-resident regions and accounting for the remaining point leaves gives at least fourteen pure point gates. This excludes all placements in this cell. [Proof by cases](seven-lines.md)

The [two-arm](two-arms/README.md) and [three-arm](three-arms/README.md) checks use the pinned samples. The [five-feature certificate](five-features/README.md) regenerates the 21 SAT instances and optional DRAT proofs. The standalone [three-special-role certificate](special3_certificate.zip) and [promoted-role certificate](zeroarm_certificate.zip) include the input and earlier point-projection dependencies. An independent reviewer checked the case coverage, the five-star equality argument and the completed DRAT verification logs. The individual checks can be replayed separately.

For width twelve, the read-once case with nine distinct line signatures has a separate [point and line cost analysis](../four-private-twelve/read-once-nine.md). The [point-cost certificates for widths 13 through 17](diagonal_fourgroups.zip) extend the four-private-group lower bounds. The existence of a 33-gate residual separator remains open.
