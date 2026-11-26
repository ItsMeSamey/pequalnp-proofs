# At most 25 live residual inputs

Every normalized seed-deleted separator for L-meta-18968 with s ≤ 33 live binary gates has n ≤ s − 8 distinct live raw inputs. Equivalently the physical excess s + 1 − n is at least nine. All seven line flags are compulsory, so n ≤ 25 implies at most 18 raw point primitives. Gate and raw counts refer to the residual after pinning and seed deletion.

The seven component archives and their SHA-256 digests are inside the combined ZIP. At excess eight the owner pattern has either one triple reader or an additional line-free endpoint. The latter splits according to whether the endpoint holds a compulsory singleton. Independent review checked that the proofs work with up to 19 point primitives and do not require using every optional coordinate. The triple-reader counts received source and coverage review. An independent execution exhausted all 1,696 empty-endpoint cases. The independent nonempty-endpoint replay reproduced all 167 baseline rows and rejected the final 48 placements. [Final branch review](last-branch-review/independent-source.md)

The six-field census now contains 255 necessary width triples. At 23 mixed gates, point width 14 with line width 8 or 9 remains. Existence of a separator still requires further work.

At physical excess nine, each occurrence of a repeated signal must be pivotal on a required positive row and on a required negative row. The rows may differ. The independent reviewer regenerated 8,528 pin cases. This necessary condition is recorded in `nine-pivotal-occurrences.zip`.
