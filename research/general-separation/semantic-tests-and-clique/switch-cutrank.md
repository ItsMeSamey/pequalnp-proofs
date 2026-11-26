# Representative prefixes for grouped Euler switches

Fix an Euler reference, let A be its symmetric zero-diagonal binary interlacement matrix, and partition its switches into an ordered sequence of h bundles. Each original optional permutation cycle of length d uses d−1 serial transposition switches; its two legal subsets relative to the reference are complementary within this bundle. Omit fixed length-one rotations. Define r as the maximum binary rank of A[L,R] when L is a prefix of whole bundles and R its complement. A valid single circuit and its switch choices can be found deterministically in time h poly(n) 8^r and space poly(n) 4^r, where n is the matrix dimension. This bound applies to bundles of arbitrary lengths and uses the supplied order. The graph preprocessing and the interpretation of nonsingular principal submatrices are given in the [switch reduction](./two-out-switches.md).

At a cut write A[L,R]=UVᵀ with q≤r columns, by Gaussian elimination. For a selected prefix subset H⊆L, define a binary vector on all T⊆[q] by

\[
v_H(T)=\operatorname{Pf}\begin{pmatrix}
 A[H]&U[H,T]\\ U[H,T]^\mathsf{T}&0
\end{pmatrix}.
\]

For a selected suffix J⊆R define w_J identically with A[J] and V. Use zero for an odd-order Pfaffian and one for the empty Pfaffian. Over the binary field these entries equal their corresponding determinants.

**Cut identity.** The Pfaffian of A[H∪J] equals the scalar product of v_H and w_J. In its perfect-matching expansion choose left and right vertex subsets P⊆H, Q⊆J used by cross edges. They have equal cardinality. The internal contributions are the Pfaffians on H minus P and J minus Q. The cross contribution is the determinant of (UVᵀ)[P,Q], since permutation signs are immaterial in characteristic two. Cauchy–Binet expands this determinant into a sum of det U[P,T] times det V[Q,T] over T of size |P|. For each T, summing over P and Q on their respective sides gives precisely the two displayed profiles, since auxiliary T vertices have no mutual edges. This proves the identity.

**Algorithm.** Start with the empty assignment. For each bundle extend every retained prefix by the two legal selections. Compute the profiles of the extended prefixes at the new cut and keep actual prefixes whose profiles form a basis of their span. At that cut, for any fixed legal suffix, a nonzero full Pfaffian for one of the extended candidates implies a nonzero full Pfaffian for a retained basis candidate. This is true simultaneously for every suffix by the cut identity. Induction over bundles therefore preserves feasibility; no coordinate change between successive profile spaces is needed. At the final empty suffix the scalar profile is the test itself. Storing the selected prefix choices gives a witness.

Each cut retains at most 2^r prefixes. A candidate profile uses at most 2^r polynomial-size determinants. Ordinary binary elimination on at most 2^{r+1} vectors of length 2^r takes O(8^r) elementary operations. These costs give the claimed bounds. With polynomial input size in h the running time is subexponential in h whenever r=o(h), and is polynomial for r=O(log n). The method also permits choosing the faster bound from this algorithm and enumeration.

The parameter can be zero with arbitrarily many four-switches. For instance, choose the base permutation to be one cycle, arrange the four tracks of each physical switch consecutively in its cyclic order, and use the all-off Euler reference. All visits to each bundle of serial crossbars are consecutive as a group, so distinct bundles never interlace. This family illustrates the parameter and has an immediate all-off witness. No bound on r for arbitrary four-switch instances follows.

The [checker](./switch_cutrank_check.py) verified cross-block factorization, a gluing identity and compressed-versus-enumerated feasibility for each of 400 seeded random alternating matrices, including non-Euler inputs, with up to twelve elements.

Rank-based representative compression for connectivity has established precedent in the work of Bodlaender, Cygan, Kratsch and Nederlof. The cut factorization above uses the interlacement matrix of the supplied Euler reference. [Primary work](https://arxiv.org/abs/1211.1505)
