# Sparse incidence queries and scalar gate reuse

For a projective plane of order q, write N = q² + q + 1. L-meta-2794 asks whether every scalar monotone circuit passing its tests must satisfy Nq ≤ 100s, where s is the gate count. The [adaptive deletion proof](incidence-deletion.md) covers orders 101 through 288. The general scalar bound remains open.

| Circuit model or hypothesis | Formal result |
| --- | --- |
| One output per point, with shared gates and line queries tested on incident singletons and disjoint masks of size at most q | Every such circuit needs at least Nq gates. [SparseQueryCut](../lean/Research/SparseQueryCut.lean) |
| Original scalar circuit, with its point input fixed to each singleton in turn | Each point has at least q original gate slots whose accepted singleton lines include two or more lines and all pass through the point. [ScalarLocalGates](../lean/Research/ScalarLocalGates.lean) |
| All but at most h gate matrices on singleton point and line inputs admit exact covers by at most r rectangles | Nq ≤ Nh + s·binom(r+1, 2). If r ≤ 9 and 2h ≤ q, the requested gate bound follows. [ScalarRankBound](../lean/Research/ScalarRankBound.lean) |

The multioutput proof traces a point’s output backward through gates whose singleton support contains at least two lines and lies inside its star. With t such gates, at most t+1 boundary wires determine the output. If t < q, the singleton positives yield a disjoint mask of size at most q that forces acceptance. Two points share at most one line, so each gate can count toward only one output. [LocalGateCut](../lean/Research/LocalGateCut.lean), [SparseBoundary](../lean/Research/SparseBoundary.lean), [UniqueStarCost](../lean/Research/UniqueStarCost.lean)

In the scalar model, fixing a different point can change the singleton support of every gate. An exact formula uses the same q qualifying slots for every point. Decomposing incidences into perfect matchings gives this overlap for every line as well. Both examples respect the target inequality. The rectangle-cover hypothesis limits this reuse because two distinct incident lines identify at most one point. [PlaneSharedSlots](../lean/Research/PlaneSharedSlots.lean), [TwoSidedSlots](../lean/Research/TwoSidedSlots.lean), [RectangleRowReuse](../lean/Research/RectangleRowReuse.lean)

Three related results examine the limits of derivative extraction, private lines in blocks of stars, and a conditional lift from singleton queries to sparse masks. [IncidenceRightDerivative](../lean/Research/IncidenceRightDerivative.lean), [BlockCertificate](../lean/Research/BlockCertificate.lean), [SparseHashLift](../lean/Research/SparseHashLift.lean)
