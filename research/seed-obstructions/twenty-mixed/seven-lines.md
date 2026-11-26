# Seven raw line inputs at 20 mixed gates

The width matrix leaves P=11 and three extra operand reads. The seven-line cell requires seven raw singleton signatures. Unfold a repeated point boundary into separate original leaf occurrences; the P-independent seven-line theorem for at most two remaining extra reads excludes this case.

Split the remaining repeated endpoints into tree regions and count s nonroot regions with exactly one original resident line. There are at most three nonroot regions.

* If s=0 use ../one-surplus/aggregate.md. If s=3 use special3_certificate.zip for b=5,6, with the b≤4 joint-output result in three-arms/README.md, ../one-surplus/three-small.md for smaller widths and b=7, or the stronger b≤5 finite run.
* If s=1 and every nonroot is line-bearing, use ../one-surplus/single-special-any-surplus.md. If the special region is the sole line-bearing nonroot, use ../one-surplus/two-endpoints-zero.md. The only other possibility has one special, one line-free region and one region with at least two residents, covered by ../one-surplus/promote-one-ordinary.md and two-arms/README.md.
* If s=2 and all nonroots are line-bearing, use two-arms/README.md. Otherwise there is one additional line-free region H and every nonroot fanout is two. Among the five ordinary point expressions, if none uses its zero-line cofactor Q, their point leaves are disjoint from the intact T,U envelopes and the same two-arm result applies. With one Q-using expression promote its target as in promotion.md, or apply the independently verified weakened three-arm role conditions. With two Q-using ordinary expressions use ../one-surplus/two-private-five.md, the tightened two-arm check through four features and its five-star equality argument. Independently, five-features/README.md verifies that the two special outputs cost at most five gates on five features. The one-promotion alternative certificate is zeroarm_certificate.zip.

Every case gives at least fourteen paid pure point gates. The resulting residual lower bound of 34 excludes a 33-gate circuit with twenty mixed gates and seven line-boundary wires.
