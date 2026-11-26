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

## Allocation table

The completed nineteen-mixed certificate gives P≥11, L≥7 and m≥20; P,L count distinct boundary wires on the point and line sides. At m=20 only 13 gates are available to the pure sides. Binary connectedness gives k=21−P−L extra operand uses beyond a tree. The exact minima of the necessary point-bank projection are 9 at width eleven, 5 at width twelve, and 0 at widths thirteen and fourteen.

| P | L | k | Point cost before the mixed exclusion | Status |
|---:|---:|---:|---:|---|
| 11 | 7 | 3 | 9–13 | Excluded by the seven-line three-surplus proof |
| 11 | 8 | 2 | 9–12 | Excluded by the eight-line support partition |
| 11 | 9 | 1 | 9–11 | Excluded by the nine-line point and mixed checks |
| 11 | 10 | 0 | 9–10 | Excluded by the ten-line matched normalization |
| 12 | 7 | 2 | 5–13 | Excluded by seven-line two-surplus theorem |
| 12 | 8 | 1 | 5–12 | Excluded by occurrence-linear eight-line one-surplus theorem |
| 12 | 9 | 0 | 5–11 | Excluded by occurrence-linear nine-line transfers plus the new width-twelve quartet checker; see read-once-nine.md |
| 13 | 7 | 1 | 0–13 | Excluded by seven-line one-surplus theorem |
| 13 | 8 | 0 | 0–12 | Excluded by eight-line read-once theorem |
| 14 | 7 | 0 | 0–13 | Excluded by seven-line read-once theorem |

The intervals are necessary bounds from width and the minimum line cost of L−7. A given line-signature family may lower the upper endpoint. The seven-line k≤2 proofs reconstruct masks using bounds linear in the actual point-leaf count; changing P does not introduce a point-width assumption. The eight-line k≤1 proofs give the same linear recovery with local case splits. This cancellation is separate from the width-specific four-group checker indispensable at P12/L9.

The eight-line checks use the [nine-paid endpoint search](endpoint-all.zip) and [ten-paid star-local search](endpoint-local10.zip).

For the nine-line point-cost replay, extract ten-line-point-cost.zip beside the tracked point-pareto directory to supply star_local.py. The two-star saturation step uses the [forest normalization lemma](two-forests.md), including overlaps between the chosen raw singleton set and the two stars.
