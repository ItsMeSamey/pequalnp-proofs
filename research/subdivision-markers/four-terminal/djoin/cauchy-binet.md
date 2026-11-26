# A randomized fixed-parameter algorithm for prescribed edges in a minimal D-join

Let G=(V,E) be a connected finite undirected graph with n vertices, let D⊆V have even size, and let R⊆E be k distinct prescribed edges. We decide whether an inclusion-minimal D-join contains R, and can return a verified witness. The algorithm is one-sided randomized, with running time 2^k poly(n,|E|,log(1/ε)) for target failure probability ε. It applies to arbitrary nonplanar graphs and dense D. Parallel edges have distinct identities. Loops cannot occur in an inclusion-minimal join. Reject prescribed loops or dependent R, and discard other loops.

A D-join has binary incidence boundary 1_D. It is inclusion-minimal exactly when it is a forest: a selected cycle can be removed while preserving all parities, and any nonempty difference between nested joins contains a cycle. Every forest extends to a spanning tree. A tree has a unique D-join, found by retaining the edges whose deletion leaves odd D on either side. Therefore the question is exactly whether some spanning tree containing R has all of R in its unique D-join. In disconnected input first require even D in each component, solve the components independently, and unite the witnesses. Isolated vertices cause no difficulty. The empty graph can be handled directly.

## The polynomial

Work in characteristic two. Let I be the vertex-by-edge incidence matrix, let w∈V be arbitrary, and let Δ=D△∂R, where ∂ is odd-degree boundary. For index sets P,Q write I[P,Q] for the corresponding submatrix. Give the ordinary edges E₀=E∖R independent indeterminates x_e. Define

\[
 P(x)=
 \sum_{\substack{A\subseteq V,\ |A|=k+1\\w\in A}}
 \det I[A\setminus\{w\},R]\!
 \sum_{\substack{B\subseteq \Delta\mathbin{\triangle} A\\ |B|=k+1}}
 \det\!\left(I[V\setminus A,E_0]\operatorname{diag}(x)I[V\setminus B,E_0]^\top\right).
\]

All determinants are square and the empty determinant is one. The polynomial is homogeneous and squarefree of degree n−k−1 unless identically zero. Its monomials are in bijection with precisely the spanning trees T for which R⊆T and R is contained in the unique D-join of T: the monomial is the product of x_e over T∖R.

**Proof.** Fix F⊆E₀ of size n−k−1. Cauchy–Binet in each inner determinant gives coefficient det I[V∖A,F] det I[V∖B,F] at the monomial indexed by F. If F has a cycle all its maximal minors vanish. If F is a forest it has k+1 components, including isolated vertices. Its minor deleting a set of k+1 rows is one exactly when those rows include one vertex from each component. Indeed each tree block has rank one below its vertex count, and after deleting one of its rows its edge columns form a basis.

For a contributing A, exactly one of its vertices lies in each component C of F. The sum over B counts, modulo two, all choices of one vertex of Δ△A in every C. It equals the product of 1+|C∩Δ| in the binary field. This value is independent of the particular contributing A and is one exactly when every component of F meets Δ evenly. The remaining sum over A is the Laplace expansion of det I[V∖{w},F∪R] along the k columns R: the rows chosen for these columns are exactly A∖{w}. Signs disappear in characteristic two. This determinant equals one precisely when F∪R is a spanning tree. Finally a Δ-join inside F exists exactly when each component of F meets Δ evenly. In this case it is unique, and its disjoint union with R is the unique D-join of F∪R. The reverse implication is immediate by removing R from the tree join. Different trees have different ordinary edge sets, so no valid monomials cancel.

## A fixed-parameter evaluation by summing minors

Only 2^k outer sets need be generated. For the k columns of R, a nonsingular row minor must select all but one vertex of each nontrivial tree component of the root forest and no other rows. Conversely all such choices give determinant one. Enumerate which vertex to omit in each component, discard selected row sets S containing w, and use A=S∪{w}. The number is at most the product of the component sizes vᵢ, bounded by 2 to the sum of vᵢ−1, which is 2^k.

At any chosen edge specialization form the weighted ordinary Laplacian L=I[:,E₀] diag(x) I[:,E₀]ᵀ. For an admitted A let M=L[V∖A,V], with l=n−k−1 rows. Deleting columns B⊆Δ△A in the inner sum is equivalent to choosing l columns J containing all mandatory columns H=V∖(Δ△A). If |H|>l or H is dependent in this specialized M, the sum is zero. Otherwise move H to the front and use invertible row operations to make its columns the first |H| unit vectors. Record the inverse determinant of these row operations (the product of the original pivot values). Every relevant maximal minor now equals this common scalar times a maximal column minor of the residual matrix N on the bottom rows and the nonmandatory columns. Characteristic two removes all permutation signs.

For completeness, the sum of all maximal column minors of an even-row matrix N equals Pf(N K Nᵀ), where K is the alternating matrix with off-diagonal entries one. The Pfaffian minor-summation identity expands this expression as the sum over maximal column sets J of det N[:,J] times Pf K[J,J]. Every even-order principal sub-Pfaffian of K is one: the number of pairings of an even set is odd, including the single empty pairing. The identity holds after reduction to characteristic two, since the signed formula is a polynomial identity over the integers. For an odd number of rows, append a zero row and zero column with a one in their shared corner. A nonzero maximal minor of this augmentation must use the dummy column and then equals its original minor. For zero rows the sum is one. Compute the Pfaffian by alternating elimination or recover it as the unique square root of the determinant in the finite binary field. This evaluates the entire inner sum in polynomial time per admitted A. [Ishikawa and Wakayama, Minor summation formula of Pfaffians](https://doi.org/10.1080/03081089508818403)

## Evaluation, one-sided error and witness

For each independent trial specialize the x_e uniformly in a characteristic-two field of size at least 2 max(1,n−k−1). A zero polynomial always evaluates to zero. A nonzero polynomial evaluates to zero with probability at most one half by the polynomial zero bound (a nonzero constant is always detected). A field of size a power of two in this range can be constructed in polynomial time, e.g. search irreducible polynomials by exhaustive enumeration at the logarithmic extension degree. Repetition gives the stated one-sided decision error.

For search, retain the distinguished edges and try deleting each ordinary edge. Keep a deletion only when the residual remains connected and a fresh amplified polynomial evaluation certifies a valid spanning tree; retain the edge otherwise. If all nonzero tests are detected, these operations leave exactly one valid spanning tree: any remaining edge outside a surviving good tree could have been deleted when considered. In that tree extract its unique D-join and verify its boundary, acyclicity and root inclusion directly. Return a witness only after verification. At most |E|+1 adaptive tests are needed per connected input so assigning each call error at most ε/(|E|+1) suffices by conditioning on the previous transcript. In disconnected input allocate the failure budget across all tests/components. The algorithm on an unsuccessful randomized run may report failure or NO, and it never returns a spurious witness.

## Root-cut patterns and scope

More generally fix a vector y on R and replace Δ by D△∂R_y, where R_y consists of roots with y_e=1. The proof then enumerates exactly the spanning trees containing **all** R whose unique D-join meets R in **exactly** R_y. Equivalently y records the D-parity on the k fundamental cuts of the prescribed tree edges. For any explicitly given affine set of accepted bit patterns, sum the resulting polynomials over its at most 2^k vectors. A tree has a unique pattern and hence contributes at most once. For a join-existence formulation in which some edges are required absent without an obligation that a common spanning tree contain those absent edges, remove them from the host before using the all-ones algorithm. The two formulations can differ.

The guarantee is randomized fixed-parameter tractability in the number of prescribed edges. The method does not give a deterministic polynomial identity test. It indexes spanning trees; several trees can extend the same minimal D-join, so it does not count distinct minimal joins.

The incidence-minor argument is a characteristic-two application of the classical all-minors matrix-tree framework. [Chaiken, A combinatorial proof of the all minors matrix tree theorem](https://doi.org/10.1137/0603033)

The independent checker pfaffian-filter.py verified 500 mandatory-column minor sums and 578 complete weighted tree-pattern evaluations over GF(8), using direct minor sums and spanning-tree/subset enumeration as its oracles. Affine pattern filtering can evaluate each allowed y separately, with at most 4^k polynomial work per trial overall.
