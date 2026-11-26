# A deterministic binary aggregate-selector algorithm

**Theorem.** Given an arbitrary represented binary matrix D, two k-bit tag columns at each physical site, and a k-bit target, one can find two words f,g in ker D of that checksum whose common-zero columns are independent in D, or decide nonexistence, in O(256^k L^8) bit operations for explicit input bit length L≥2. This conservative bound also gives uniform polynomial time for k=O(log L). The returned words produce the exact k+1-root aggregate contraction witness. [Physical aggregate representation](../aggregate-flow-selector/README.md)

## Dual reduction to unequal labels

Let T_e be the column at site e of a full-row-rank generator for ker D, and let V be the span of the T_e. The two codewords are exactly the evaluations h(T_e) of a linear map h from V into the two-bit space. A set Z of common-zero columns is independent in D exactly when the active T_e outside Z span V. Failure of span gives a nonzero codeword vanishing on all the active positions, equivalently a nonzero dependence of D on Z.

Write τ_e,1 and τ_e,2 for the k-bit tag vectors. For each checksum bit j define two vectors in V by summing the T_e with (τ_e,i)_j=1 in lane i. The prescribed equation is the sum of the first evaluation bit at the lane-one vector and the second bit at the lane-two vector. Let U be the span of these at most 2k vectors and d=dim U. Enumerate all 4^d assignments h restricted to a basis of U and retain those satisfying the k equations.

The recursive problem allows an arbitrary two-bit forbidden offset o_e on each indexed column. Given the prescribed restriction on U, find h for which the columns with h(T_e)≠o_e span V. Initially all offsets are zero. Repeated columns, repeated labels, loops and zero-dimensional spaces are allowed.

## A full basis or a rank deficit

Make two copies of each physical index e. In the first matroid the copies have identical column T_e. In the second put the class of T_e modulo U in the first or second summand of (V/U)⊕(V/U), according to its copy. Run ordinary maximum-cardinality linear matroid intersection. The implementation uses shortest augmenting paths and the final reachability certificate. [Edmonds, Matroid Intersection](https://www.sciencedirect.com/science/article/pii/S0167506008708173) · [Lawler, Matroid Intersection Algorithms](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1971/Archive/ERL-m-333.pdf)

If a common set has size r=dim V, its physical columns are a basis of V. In lane i its chosen columns are independent modulo U. For these columns prescribe evaluation bit i opposite to bit i of o_e, and extend the functional from U by elimination. Do this separately in both lanes. Their pair activates every basis member. A physical index cannot be selected twice, since its copies are parallel or loops in the first representation.

Otherwise let S be the min-max certificate, with rank_first(complement S)+rank_second(S)<r. Failed augmentation gives S as the reachable elements when sources are addable in the first matroid. Define Y to consist of physical indices having both copies in S. The first rank is rank(T outside Y), and the second rank is at least twice the rank modulo U of T on Y. Put Z=span(T on Y), B=span(T outside Y), R=dim Z, u=dim(U∩Z), and λ=dim(Z∩B). Since V=Z+B, the deficit says

    dim B + 2(R−u) < r = dim B + R−λ,
    hence R+λ<2u.

In particular R<2d, λ<u, and a=R−u<u−λ. The argument counts indexed copies separately even when physical columns coincide.

## Removing the deficient set

Enumerate the 4^a extensions h₀ of the prescribed map from U to W=U+Z. For one extension let A be the span of the Y columns activated by h₀. If A+B differs from V, reject this branch. Otherwise the remaining columns span V/A after projection π. This last check is essential. Fix a linear section s of π. On each remaining column x the new forbidden offset is

    o'_x=o_x+h₀(x−sπx).

The new pin space is U'=πW=W/A. Since A⊆W, each representative sπw of a vector w in W still lies in W. Prescribe h'(πw)=h₀(sπw). Any extension h' on V/A lifts by

    h(x)=h'(πx)+h₀(x−sπx).

This formula is linear, agrees with the chosen branch on W, and activates each retained index precisely when its projected value differs from its new offset. Conversely every h extending the branch has this form. Zero projected columns can change activity without affecting rank. The previously active Y columns span A, so the new activated set spans V/A exactly when the old one spans V. The explicit implementation takes echelon remainders for the section and reconstructs both covectors on the original ambient coordinates.

Every viable branch has dim A≥R−λ since A+B=V. Consequently its pin dimension obeys

    d'=d+R−u−dim A ≤ d+λ−u,
    a+d'<d.

The problem strictly decreases even when one has fixed additional local values. A full basis ends recursion. At d=0 a deficit would contradict R+λ<2u. Empty ambient spaces accept with the zero map.

## Running time, code and scope

Counting all candidate branches, one node of pin dimension d has 4^a candidates and every viable child has d'≤d−a−1. With polynomial work per node and per local candidate, induction bounds the number of these work units by O(4^d). For example 1+4^a(1+2·4^{d−a−1})≤2·4^d for d≥1 and a≤d−1. The initial pins add at most another factor 4^d, giving 16^d≤256^k. In the explicit binary model the dimensions, columns and k are at most L (an explicitly listed site consumes an index when the representation has empty rows). At each augmentation there are at most 2m represented columns and O(m²) exchange pairs, and at most m augmentations. Even recomputing Gaussian independence tests from scratch costs O(L³) binary operations per pair. Building all matrices, all section applications, rank tests and witness interpolation fit inside the displayed O(L^8) conservative work bound for a node or a single local candidate. Storage of an exponentially large search tree is unnecessary.

Run `python check.py` with the sibling `unseeded-root-states` helper. The code implements the full deterministic intersection, deficit, recursion, and physical word recovery. The tests compared 163 affine-offset instances with all linear maps and 396 aggregate target queries on 63 represented hosts with exhaustive word pairs. They reconstructed and checked all 222 resulting exact named kernels by Gaussian elimination on the physical columns. Dedicated controls include F₇, F₇*, the regular cographic M*(K₃,₃), repeated columns, ambient and pin dimension zero, U=V, and nonzero offsets. Additional independent comparisons used a brute-force separator minimizer on 1,000 systems, and a separate three-bit algorithm on 1,280 target queries.

The result solves this specific aggregate-line construction over every binary host. The physical result for a valid pair uses one selected column at a nonzero site and all three columns at a zero site. It does not enforce strict coverage at every coordinate, minimum contraction cardinality or an arbitrary prescribed named kernel. Those additional requirements have different decision predicates.
