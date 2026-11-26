# Joint linear local-distribution and polynomial-calculus lower bounds

Use any bounded-degree compiled hard graph FPHP family from the [guarded pigeonhole construction](README.md). Let e be any unmatched-pigeon edge. With only x_e set to one, the old marker holds and the only violated guard is at e. Modify that guard by adding a fresh bit a_r to its affine factor. Take a connected, bounded-degree edge expander H on n vertices comparable to the old number of variables. Add one pivot a_v per vertex and z_f per edge, and the guards over GF(2)

    a_v (sum_{f incident to v} z_f + [v=r]) = 0,
    z_{uv} (a_u+a_v) = 0.

Summing all new guards gives a_r = 0, since each incidence contributes twice. Thus the resulting formula is unsatisfiable. Setting all new bits to zero restricts it to the hard old instance, preserving its PC degree and ordinary PC size lower bounds. All rows retain distinct unit pivot representatives, the sole marker gives deficiency exactly one as before, and both degree bounds are constant.

For the local marginal hierarchy set x=e and all a_v=1. Only the inconsistent odd-charge Tseitin constraints on the z variables remain. Suppose the edge expansion of H is h>0 for sets up to n/2. For every queried edge set S of size less than hn/2, H minus S has a unique component larger than n/2. Indeed, if every component had size at most n/2, summing their outgoing edge counts gives hn at most 2|S|. Pick a defect vertex w in that giant and take the uniform distribution over all full edge assignments whose incidence parities have the prescribed charge vector flipped at w. This corrected vector has even total parity and hence solutions by a spanning tree elimination. Project onto S. This projection is independent of w in the giant, since flipping along a path between two candidate defects that avoids S bijects the solution spaces and preserves S. For S contained in T, the giant after removing T is inside that for S, giving exact projection consistency. If S contains all edges of a vertex, that vertex is isolated and lies outside the giant, so its parity is always satisfied. Extend each distribution by the deterministic bits above. This yields marginals on all variable sets up to a linear budget, satisfying every guard and marker on any containing set. In particular it fools any Sherali–Adams lift of linear clause inequalities encoding each bounded-width factor through a linear number of rounds (allowing the constant budget for factor variables). The same marginals also cover full-bag overlap consistency. The hard PC and local faces are different restrictions of the same family.

Choose the auxiliary edge expander independently on a comparable number of vertices. No algorithmic conclusion for unrestricted proof systems follows from these bounds.
## A degree-two preprocessing step

Multiply the derived line a_r=0 by x_e and add it to the shifted guard. The [base mask LP](README.md) now certifies a contradiction on the restored old rows. This gives a short combined proof despite the separate lower bounds.

## Sherali–Adams encoding of the incidence switch

For each Boolean guard or marker on scope U, evaluate its affine sums over GF(2) to form its forbidden assignments. For each forbidden assignment b, introduce the clause with positive literals at b_i=0 and negative literals at b_i=1. Its real inequality is g_b(x) = sum_{b_i=0} x_i + sum_{b_i=1} (1−x_i) − 1 ≥ 0. At Boolean x this takes value dist(x_U,b)−1. Hence the simultaneous inequalities encode exactly the row relation. This applies even when the pivot occurs in its mask: use one variable per distinct bit and the actual row truth table. The constant maximum arity w bounds the number of clauses per row by 2^w.

Write h for the edge expansion and m for the vertex count of the switch graph. After pinning the old bits to the distinguished singleton, and a_v=1, the old rows and marker hold and only odd-charge Tseitin stars constrain the unpinned edge bits. For every network set S of size <hm/2, take the distribution constructed above on its edge coordinates and give the fixed coordinates their prescribed values. It puts probability one on legal values for each relation whose scope lies in S. Indeed a vertex with all incident edges queried is isolated in the graph with the queried edges removed and cannot host the hidden defect for m≥3. These marginals agree under projection.

Define a real functional on squarefree monomials by L[x_A]=Pr[all coordinates in A are 1] in the A-marginal. Compatibility implies that on any multilinear polynomial supported on S its value is its expectation in the S-marginal, by expanding in monomials. In particular L[1]=1. For a product M of at most k positive or complemented literals, the union of its variables and a clause scope has size at most k+w. If k+w<hm/2, L[M g_b] ≥ 0 follows from the honest expectation over this union, since both factors are nonnegative on its support. The same holds for every valid real linear inequality on a single factor and the variable bounds. Boolean reductions such as x_i²=x_i preserve every such expectation. This yields feasible SA moments in the convention allowing conjunction multipliers of length k, regardless of whether rounds are indexed starting at zero or one. If a factor is given by its real multilinear falsity indicator as an equality, its products have expectation zero by the same argument. No real arithmetic interpretation of the original GF(2) polynomial is used.

## Elementary switch graph existence for every order

For m>=3 superimpose the undirected edges {v,pi_i(v)} of twenty independent uniform permutations on [m], deleting loops and merging parallel edges. The simple graph has maximum degree at most forty. If some s-set S, 1<=s<=m/2, has at most s/10 exterior neighbors, there is a set J outside S of size j=floor(s/10) such that every permutation maps S into S union J. For fixed S,J this has probability at most (1.1s/m)^(20s), since each image is sampled without replacement. The union bound for fixed s gives

    binom(m,s) binom(m-s,j) (1.1s/m)^(20s)
    <= [e (10e)^0.1 (1.1)^20 (s/m)^18.9]^s < (1/1000)^s.

For j=0 the second binomial is one. For j>0 use that (em/x)^x increases up to m to replace j by s/10. The numeric bound follows by setting s/m=1/2. Summing over positive s gives probability less than one. Hence at every m there is a simple connected graph with edge expansion at least 1/10, since each exterior neighbor contributes a distinct crossing edge. Choose m equal to the number of old variables to balance the two restrictions. This existence argument requires no deterministic expander theorem.

The [finite checker](check_expander.py) enumerates a complete bipartite base graph and a five-vertex complete auxiliary graph, verifying the restrictions, parity cancellation and local distributions.

The same forbidden-assignment encoding has [linear real sum-of-squares degree](sos.md), both for the quadratic module and for the stated degree-charged preordering.
