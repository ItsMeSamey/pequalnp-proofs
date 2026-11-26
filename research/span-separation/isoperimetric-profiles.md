# Beyond linear vertex expansion

Let bounded-degree graphs satisfy an external-neighbour bound f(k) on every k-vertex set of size at most n/2, for a fixed computable nondecreasing unbounded function f. The proof in expander-arbitrary-labels.md applies to a biconnected such graph with the following substitutions.

Choose a computable integer Q(c) with f(Q(c))>c. Unboundedness and approximating f from below give such a certified threshold without deciding equality of computable reals. After deleting at most c vertices, if a remaining component has more than Q(c) vertices it contains over half the original graph. All remaining components then have total size at most Q(c). For an anchor of demand d_i use a connected set of any fixed size a_i with f(a_i)>d_i. If its enlarged set has size at most n/2 its exterior has at least d_i vertices, as required for separator charging. Recompute the entire finite frequency staircase with these bounds, including Q(c) for each local hole-growth bound. The bounded-degree ball-volume estimates still apply.

The requisite fixed K_M model may be supplied. It is automatic for large n if f(x)/√x tends effectively to infinity: absence of K_M supplies a balanced separator of size at most M^(3/2)√n with both shores of size at most 2n/3. For large n the smaller shore has at least n/6 vertices; the inequality f(floor(n/6))>M^(3/2)√n then contradicts its boundary size. This inequality can also be tested directly as a sufficient size condition.

For an arbitrary connected host, centroid pendants have at most Q(1) vertices. The biconnected centroid block inherits the profile f/Δ by the previous shore-lifting and crossing-edge argument. Apply the model criterion on this block. For slower profiles, require a sufficiently large clique minor on that block in addition to its isoperimetry.

In particular for fixed f(x)=αx^β with α>0 and β>1/2 the proof gives a deterministic polynomial-time witness and decision algorithm for arbitrary binary labels of fixed dimension and fixed part count, on bounded-degree graphs obeying the profile. The ratio f(x)/x may tend to zero.
