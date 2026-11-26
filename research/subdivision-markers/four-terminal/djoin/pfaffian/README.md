# A one-sided randomized algorithm for rooted minimal joins

In a connected undirected multigraph with n≥1, let I be its binary incidence matrix, with zero columns for loops. Let R consist of k distinct marked edges, let D be an even set, and put Δ = D △ ∂R. Reject if k≥n or R is cyclic. Root at an arbitrary vertex w.

Every minimal D-join is a forest and extends to a spanning tree. Conversely a tree has a unique D-join obtained by leaf elimination. Let P(x) be the multilinear polynomial having one monomial ∏_{e∈T−R} x_e per spanning tree T containing R whose unique D-join uses all of R. Edge variables are distinct even for parallel edges. Over characteristic two this is a nonzero polynomial exactly when a witness exists.

## Cofactor identity

Enumerate A of size k+1 containing w, retaining those with det I[A−w,R]=1. Each nontrivial tree component C of R contributes all its vertices except one to A−w. If w is in C, its omitted vertex must be w. No isolated vertex contributes to A−w. Enumerating omitted vertices directly gives at most ∏_C |C| ≤ 2^k admissible choices. The independent checker instead filters up to binom(2k,k) endpoint choices by elimination. Set S=Δ△A. Form

    Y = I[V−A,E−R] diag(x) I[V,E−R]ᵀ.

For each such A sum det Y[:,V−B] over all (k+1)-sets B⊆S, and then sum those answers over A. The result equals P.

Indeed, Cauchy–Binet gives the coefficient of a fixed (n−k−1)-set F of unmarked edges as the sum of det I[V−A,F] det I[V−B,F]. The first determinant vanishes unless F is a spanning forest with exactly one A vertex per component. Under that condition the second demands one B vertex per component. Their number modulo two is ∏_C |C∩S| modulo two, which equals ∏_C (1+|C∩Δ|) modulo two independently of the admissible A. Thus F contributes zero unless every component contains evenly many Δ vertices. If they do, the remaining sum over A is exactly the Laplace expansion of det I[V−w,F∪R] on the R columns. This determinant is one precisely for a tree. The componentwise parity condition is equivalent to the existence of a Δ-join inside F. Adding R gives the unique D-join in that tree, with all marks included. The argument handles isolated components, k=0 and empty cofactors.

## One Pfaffian per A

Use an alternating matrix with zero top-left block, upper-right block Y and lower-right block the adjacency matrix of the unit-weight complete graph on S within the n bottom vertices. If k+1 is odd, append one extra bottom vertex adjacent exactly to S, with zeros to every top vertex. Its Pfaffian is the desired sum over B. In the matching expansion every top vertex matches to a distinct ordinary bottom vertex. The uncovered ordinary bottom set B has k+1 vertices. Its completion, including the dummy if present, is impossible unless B⊆S, and otherwise the number of completions is an odd double factorial. The cross-match sum is det Y[:,V−B] in characteristic two. No external Pfaffian-orientation theorem is required.

Pick independent uniform x_e in GF(2^h) of size at least 2n. The degree of P is at most n−k−1, so a feasible instance evaluates nonzero with probability at least one half, and infeasible instances always evaluate to zero. Time is O(2^k poly(n,m)) field operations per trial. Construct the field by deterministic irreducible polynomial search of degree h=ceil(log₂(2n)); even exhaustive trial division is polynomial in n. Repeat independently for any desired false-negative error.

A nonzero evaluation yields a witness without further randomness. For an unmarked nonloop e, its polynomial satisfies P_G=P_{G−e}+x_e P_{G/e}, retaining the marked edges and replacing terminal demands on the contracted vertices by their XOR. Spanning trees avoiding e survive deletion. Those using e correspond under contraction, and the unique join on the contracted tree lifts uniquely across e by restoring the parity at either original endpoint. Mark usage is consequently preserved; e itself can be outside the join. Evaluate the deletion at the same remaining field values. If nonzero, delete e; otherwise contract e and record it as part of the spanning tree. The contraction polynomial must then be nonzero. Unmarked loops can always be deleted. Once only marked edges remain, nonvanishing forces them to form a spanning tree on the contracted graph. Uncontracting the recorded edges recovers a good original tree and leaf elimination recovers its D-join. This adds at most m further evaluations. A zero first evaluation may be retried independently. Componentwise instances with even demands in each component decompose without connecting them.

The checker compares the compressed Pfaffian formula to independent spanning-tree enumeration over GF(16) and also compares all Boolean evaluations of small homogeneous polynomials, which determines every coefficient by Boolean Möbius inversion.
