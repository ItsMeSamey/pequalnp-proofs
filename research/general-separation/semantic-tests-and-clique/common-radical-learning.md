# Comparing the two cap supports while learning common kernel vectors

Use the binary principal representation K=I+M₀⁻¹ of an original graph and three pins P. Write F for its exterior sites, B=K[P,F] and J=K[F,F]. At an exterior subset S the two [cap channels](even-odd-extension-cap.md) indicate whether some even or odd pin subset can be appended to S to give a feasible binary principal submatrix.

Both channels vanish at S exactly when a nonzero binary vector v on F satisfies

    supp(v) ⊆ S,    (Jv)|_S = 0,    Bv = 0.

Such a vector remains in the kernel after appending any pin subset. Conversely eliminate a nonsingular principal block of J[S] of size rank J[S]. The remaining zero block has size equal to its kernel dimension. If B acts injectively on that kernel, choose the same number of pin coordinates whose rows restrict to a basis there. The resulting bordered matrix has diagonal blocks zero and an arbitrary symmetric matrix, and an invertible square cross block. It is nonsingular. With an empty kernel no pins are needed. Ordinary binary linear algebra thus gives either the common kernel witness or confirmation that some channel succeeds.

Let r be the dimension of the span of all these common kernel vectors, across all S. There is a deterministic decision and original-witness algorithm with at most r successful learning rounds and time (2n)^{r+O(1)} n^{q+O(1)}, q=16 and n=|F|+3. Its memory is polynomial even without knowing r or being supplied with any subspace.

Start with no learned vectors. Suppose their independent columns form U with k columns. At a candidate S form W(S) with one row per exterior site. Its row i is U_i when i is absent, or (JU)_i when i is present. A nonzero learned combination certifies common failure exactly when W(S) has nonzero kernel: each column of U is already killed by B. In particular, W(S) has full column rank at any distinguishing S.

Enumerate k distinct sites and their two inclusion values so the selected rows are independent. For k=0 use the single empty choice. For each resulting partial assignment seek a singular exterior of either cap slice using the [short-obstruction search](minimal-singular-principal-search.md), with its mandatory border and prescribed site values. If neither slice ever has a singular extension, the supports agree: any distinguishing exterior would have some full-rank k-row certificate and one singular channel. If a returned exterior is missing from just one slice, replay its eight pin extensions and recover the original witness. If both slices miss it, solve for v as above. The fixed independent rows guarantee v lies outside the span of U. Adjoin v and restart. Each restart raises k, with k≤r. One final round terminates. Each round tries at most 2^k times the binomial coefficient (|F| choose k) partial assignments. The space and field-operation bounds follow.

## Exponentially many common failures with one learned direction

Take an isolated unpinned vertex, a path of m unpinned vertices whose end is joined to pin 1, and a disjoint edge between pins 2 and 3. Requiring both endpoints of that edge makes the physical instance NO. In any full raw loop completion a kernel vector vanishing at the pins and satisfying the pin equations vanishes along the whole path: pin 1 forces the first path site to zero, and then its row forces the next one, successively. The isolated site can support a nonzero private vector precisely when its raw diagonal is zero.

To see the same restriction in the coordinates used by the algorithm, extend any common vector v by zeros on the pins and off S. Put w=M₀⁻¹v. Then w agrees with v on S and vanishes on P, by the two kernel equations. Consequently (M₀+diag 1_S)w=0. The forced propagation shows that w, and hence v=M₀w, is supported on the isolated site. Conversely its base diagonal is necessarily one and toggling that site makes its unit vector a common witness, independently of the other m flips. Thus r=1 and exactly 2^m masks are missing from both channels. Counting common missing masks and counting independent kernel directions give different algorithmic guarantees. For general graphs r can grow with the input.
