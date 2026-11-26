# Covering a terminal affine slice by guard violations

For any set of optional bits with native affine-disjunction guards, let A be the affine solution space of the supplied terminal equations. An inconsistent A rejects immediately. Guard i is violated on a flat F_i within A defined by its head equal to one and each of its affine truth indicators equal to zero. Gaussian elimination discards empty flats and computes each cardinality. Let N be the number remaining. This method also applies to cyclic guards and arbitrary affine disjunctions. Terminal disjunctions can first use the projection in ../clause-projection.md when their number is a parameter.

Sort the nonempty flats by decreasing cardinality, using a fixed order to break ties. For a prefix C of l flats write G=A minus their union. Inclusion–exclusion counts G exactly in O*(2^l) time. It also counts G intersected with any affine slice at the same cost. If G is empty, no solution exists.

A sufficient structural criterion is

    sum over i outside C of |F_i|/|A| < 2^(-l).

Indeed if G is nonempty, take an arbitrary x in G. For each of the l flats some defining affine equation fails at x. Fix this failure as an affine equation. The resulting intersection in A contains x, avoids every flat of C, and has codimension at most l. Consequently |G| >= 2^(-l)|A|. The displayed inequality implies a positive count after subtracting the sum of the remaining flat sizes. An easily checked coarser condition is that all remaining codimensions exceed l+log2(N) for N>0.

The implementation uses the stronger signed lower bound on every subspace B of A

    W(B) = |B intersect G| - sum over i outside C of |B intersect G intersect F_i|.

On a point in G this is one minus its number of tail violations. On other points it is zero. Hence W(B)>0 guarantees a full solution in B. Search increasing l until |G|=0 or W(A)>0; at l=N one test must succeed. W is additive on the two disjoint half-slices fixing an individual variable. Starting with W(A)>0, choose a zero half when its weight is positive and the one half otherwise. After all bits have been fixed the unique point has positive weight and therefore satisfies every guard. Signed weights of the two halves need not be nonnegative. This argument uses only their sum. The weaker raw codimension criterion already ensures this exact conditioned test stops by l. With l the first terminating prefix length, the total time is O*(2^l) and the direct loop uses polynomial space. All integer counts have polynomial bit length. Guard order and rank are unrestricted.

## Sparse long cycles and conditioned counting

For every even n>=12 use unrestricted bit x0 and guards x_i=1 implies x_(i-1)=1 for i=1,...,n-1. Add the extra alternative x0=1 at the last guard. The undirected dependency graph is a single chordless n-cycle, each guard reads at most two bits, and the directed instance remains acyclic. Use n−2 binary terminal equations identifying all even bits with x0 and all odd bits with x1. In A the violations alternate between two different singleton points (0,1) and (1,0), and the extra final alternative agrees with its existing one. Every violation has codimension two. With the native order the first two flats remove both possible types, so all subsequent conditioned intersections are empty and the algorithm stops at l=2. The raw displayed criterion requires every flat in the prefix. This example illustrates rank-independent handling of many terminal markers.

For a separation that survives merging equal flats, take two free bits x0,x2, guard x1 implies x0, and for j>=3 the guard x_j implies (x0 OR NOT x1 OR x_(j-1)). Use no markers. The first forbidden flat has codimension two. Each later forbidden flat has codimension four and is a distinct strict subset of the first. At n>=24 the raw criterion fails for l=0,1, while the exact conditioned test succeeds at l=1 (and fails at zero). Since inputs have O(n) literal occurrences these are sparse instances with bounded guard arity. A preliminary flat-containment elimination would find this redundancy directly.

For a dense shared DAG with l=0, let the first eight bits be free, and give every later bit the alternatives NOT x_j for all its predecessors. Under a single odd-total-parity marker and n>=32, the rank of all-i-prefix pins is i+1 in the ambient space. Their relative densities are at most 2^(-i) on the marker slice, so the total is below one. The graph has unbounded depth, indegree and sharing.

flat_solver.py implements adaptive conditioning and bit-by-bit witness recovery. test_flats.py exhaustively compares 1,803 marker slices of seeded small systems and directly validates the dense, cycle and strict-subflat examples. This result is fixed-parameter in the number of exceptional flats under the stopping test. It gives no bound on that parameter from terminal-marker count alone.
