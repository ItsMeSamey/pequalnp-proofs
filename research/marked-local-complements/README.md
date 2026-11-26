# Parity markers under local complementation

Let A be the symmetric zero-diagonal adjacency matrix of a simple graph on n vertices. For x over GF(2), put y=Ax. The set D(x) of indices with xᵢyᵢ=1 records the selected vertices of odd induced degree. A witness has D(x) empty and Lx=z for a specified t-row marker matrix L and target z. Write Lᵢ for the column at vertex i.

**Twin-port characterization.** Add a pair of ports pⱼ,qⱼ per marker, both adjacent to all original vertices i for which Lⱼᵢ=1. Put in the edge pⱼqⱼ exactly when zⱼ=1. Initially leave edges between different pairs absent. There is a witness exactly when local complementations centered only at original vertices can make every paired edge absent simultaneously. Other port edges at the end are unrestricted. Whenever this is possible, a sequence suffices that uses each center at most once. This is a certificate equivalence. Finding the sequence by enumeration can take exponential or greater time.

## Transport of assignments and defects

Local complementation at v toggles every edge between distinct neighbors of v. Write a=Aeᵥ. The new matrix is A′=A+aaᵀ+diag(a). Map x to x′=x+eᵥ(1+yᵥ). Then y′=A′x′=y+a+diag(a)x, using aᵀx=yᵥ and aᵥ=0. At v the pair becomes (xᵥ+1+yᵥ,yᵥ). At a neighbor i it becomes (xᵢ,yᵢ+1+xᵢ). At all other indices it stays fixed. Each pair transformation preserves its product, including at defective vertices. Complementing twice at v recovers the matrix and assignment.

Set L′=L+Lᵥaᵀ and z′=z+Lᵥ. Since aᵥ=0, direct multiplication gives L′x′=Lx+Lᵥ. Thus the entire marker residual Lx+z and the entire indexed defect set are preserved for every assignment. This refines the unmarked count identity that the number of induced even-degree supports equals Q(G,4)/2ⁿ and is invariant under local complementation. [Aigner and van der Holst, Interlace polynomials](https://www.sciencedirect.com/science/article/pii/S0024379503006761)

The augmented graph implements these two updates by ordinary local complementation. For each port pair its edges to i toggle precisely if i is adjacent to v and both ports are neighbors of v. Its paired edge toggles precisely if its label bit at v is one. Other port-to-port edges may change, but cannot affect these updates while only original vertices serve as centers.

From a witness, complement at any selected vertex v. Its yᵥ=0, so the transformation removes it and fixes every other coordinate of x. Repeating gives x′=0 in exactly the original support size steps, at distinct centers. Since the residual stays zero, the final target is zero. Conversely, from any sequence ending with all paired edges absent the zero assignment is a witness there. Reversing the sequence and the affine coordinate maps recovers an original witness. These arguments also explain how to convert either type of certificate into the other.

## Three-marker normalization

For arbitrary x, complementing only at selected vertices outside D(x) shrinks the support to exactly D(x), preserving the marker residual. For a consistent system of three linear markers first choose an assignment with support of size at most three by expressing z in a basis of the columns of L. Inconsistency is detected by elimination. The number of defects is even because xᵀAx=0. Thus the sparse candidate has zero or two defects. In the former case it is a witness. In the latter, at most one complementation removes its selected nondefective vertex. Its two surviving vertices are adjacent, since each has odd degree inside that pair, and their updated marker columns sum to the updated target. This gives an equivalent instance with a target-matching adjacent pair. The pair violates its two guards, so deciding whether another assignment is a witness remains necessary.

Run python -B check.py. The checker compares directly attainable marker vectors against paired-edge patterns obtained by all sequences of distinct centers on every graph and two-bit labeling through three vertices. It verifies individual defect and marker transport on every assignment in these cases. A further 1,000 seeded three-marker instances test the sparse normalization and the port encoding.
