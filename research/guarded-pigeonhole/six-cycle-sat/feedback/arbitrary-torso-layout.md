# Compiling Pfaffian factor trees with unbounded torso arity

Work over the binary field. Each supplied tree node has an alternating matrix A indexed by pairs. Its table on a bit assignment is the Pfaffian on exactly the selected whole pairs. A physical bit belongs to one node and a virtual bit belongs to the two ends of its tree edge, with equality and summation at that edge. Local bit complements may be recorded in the coefficient slices. Such factors occur after whole-pair rank-two splits by the bordered Pfaffian expansion. Supply a pair order at each node whose maximum prefix-to-suffix matrix rank is r. Write N for the explicit input size including these matrices and trees. No restriction on torso arity is required.

## The prefix signature and its transition

For a prefix P of individual indices ending between pairs, choose a column basis U of A[P,complement(P)], of rank t≤r. For a selected union X of prefix pairs, define a vector indexed by even subsets L of the t basis indices,

    σ_P(X)[L] = Pf [ A[X,X]    U[X,L] ]
                    [ U[X,L]ᵀ     0    ].

Use Pf(empty)=1. The coordinate count is one when t=0 and otherwise 2^(t−1). The entire selected prefix X has even size, so odd borders need no coordinate.

For the next pair g and choice b, let Y contain both gate indices if b=1 and none otherwise. Choose the new cut basis U' in the same way. To compute the coordinate indexed by an even subset L' of the new basis, let E consist of Y and the new border indices L'. Write D for the alternating block on E, comprising the gate block, its incidences U'[Y,L'], and the zero block on the new border. The cross matrix from the entire old prefix P to E has the form U H. Indeed, columns to Y are old suffix columns and the restriction of U' to P consists of combinations of old suffix columns. The basis choices, H and D are independent of the selected X.

For every even old-border subset L set

    K_b[L',L] = sum over J⊆E, |J|=|L| of det H[L,J] · Pf D[E minus J].

Then σ_{P∪g}(X∪Y) = K_b σ_P(X). To prove the formula, expand the new Pfaffian by the old and external endpoints matched across the cut. For cross endpoint sets I⊆X and J⊆E of equal size, cross matchings sum to det(U[I,:] H[:,J]) in characteristic two. Cauchy–Binet expands this into det U[I,L] times det H[L,J]. Summing over I with the internal factor Pf A[X minus I] yields σ_P(X)[L] because every old border vertex must match into X. Odd |I| leaves odd |X minus I| and contributes zero. This also proves the recurrence when restricting to X lowers the rank.

One can construct smaller matrices without explicitly expanding K_b. Begin with the empty prefix and its one actual representative. At each layer extend each currently retained mask with both choices and compute its new signature directly by bordered Pfaffians. Retain a maximal independent subcollection of these actual signatures and record every extended vector in its coordinates. The two resulting transition matrices are valid on the full reachable span by the proven recurrence. At the end the sole cut coordinate is the unbordered Pfaffian. Use the final scalar values of the retained basis as the output functional. This gives an explicit read-once oblivious arithmetic branching program on local pair bits, of width at most 2^r. Building it takes 2^O(r) poly(N) binary operations by elimination and polynomial-time numerical Pfaffians. The supplied order's cut ranks can also be checked by elimination.

## Combining distinct layouts

Replace each torso node by the path of its transition tensors. A physical layer supplies its two coefficient matrices as A₀+h_i A₁. Leave the selector of each virtual layer as an unweighted binary tensor index, and connect its unique two copies by the original tree edge. The contraction sums a common bit once. A path replacing a vertex of a tree preserves connectedness and acyclicity, since contracting all substituted paths recovers the original tree and each original edge was a bridge. Empty constant factors can be absorbed. Each new tensor has at most three incident bonds, each of dimension at most max(2,2^r); each physical tag appears in one layer.

Order this expanded tree recursively by visiting its largest child subtree, then the vertex, then all other child subtrees. During the largest-child visit the vertex and other subtrees are untouched. During any other child visit the remaining local frontier uses at most three edges and that child's subtree size is at most half the parent's. Thus each prefix crosses O(1+log N) bonds. Storing their index assignments and contracting one bounded-degree tensor at a time constructs a global program of width N^O(r+1) in the same time bound. The two pencils can have different trees and different physical orders. For their sum with the width-one envelope, the deterministic white-box test for three such programs takes N^O(r+1) time. To recover a nonzero physical mask use coefficient restrictions, substituting the constant or linear matrix of the chosen layer in each program. See [different-order tree comparison](different-order-trees.md) and the [white-box identity theorem](https://doi.org/10.1007/s00037-016-0141-z).

The independent [prefix checker](check_torso_prefix_audit.py) constructs the representative transitions and compares every resulting coefficient with a separate direct recursive Pfaffian. It checked all 6,300 masks on 300 seeded alternating matrices with one to six pairs. This tests the local recurrence and reconstruction of scalar coefficients. The global compilation and runtime bounds above are proved analytically.
