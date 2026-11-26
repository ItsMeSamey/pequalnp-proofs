# Preserving a binary terminal trace profile under bounded edits

Let E be finite binary columns in V, W its interface, and b≥0. Replace each labelled e by b+1 private paths of length b+1. For a path of length L introduce L−1 independent private vectors. The ith column is p_(i−1)+p_i with p_0=0 and p_L=e. Private vectors are disjoint across paths. Every binary combination with vanishing private coordinates uses all or none of each path because adjacent coefficients must agree. A complete path sums to e.

Contract any C and delete any disjoint D with |C|≤b, |D|≤b. No entire path lies in C, so span C intersects V trivially and W embeds in the quotient. For any remaining selection X and v∈W, v lies in the selected span after contraction precisely when v is in span(C∪X). Its intersection with V is spanned by exactly the old columns having at least one path wholly in C∪X. Every resulting trace is thus an old trace.

Conversely, for every e in any requested old subset, at least one of its b+1 paths is unbroken by D. Select all noncontracted columns of one such path for each requested e. Every other path is incomplete because it contains at most b contracted columns. Thus the trace of every old subset is attained, also for zero or repeated columns. The full W trace catalog is unchanged under both edits.

Applied to two indistinguishable catalogs for boundary-only rooted queries, this replacement tolerates even adaptively chosen ordinary edits if the cumulative bounds on contractions and deletions for each query hold. Access to the full matrix or rooting ordinary generators can reveal other information. The construction uses (b+1)^2 columns per old element.
