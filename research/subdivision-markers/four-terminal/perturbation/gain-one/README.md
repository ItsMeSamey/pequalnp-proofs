# Gain-one circuits for one additive direction on a graphic representation

Let B be the binary incidence matrix of a finite undirected multigraph, with a zero column for a loop. For a nonzero binary vertex vector u and an edge-bit vector γ, set A=B+uγᵀ. Given k marked edge IDs R, seek a circuit C of A containing R with γ(C)=1. Here γ(S) is the parity of selected gain-one edges. Necessarily ∂C=u. Reject this branch when u is outside the incidence span, equivalently when some connected component meets u oddly. Otherwise connect the components by arbitrary new bridges of gain zero, keeping the original D=u. Every u-join uses none of these bridges, by summing parity on either side. No cycle uses one. Hence the gain-one query is unchanged. From now on the graph is connected on n vertices. When u=0 the matrix is just B, and this proof does not supply the ordinary cycle query.

For an edge set C of boundary u and gain one, C is a circuit of A exactly when its ordinary cycle space contains no nonzero gain-zero vector. Indeed any second nonzero A-dependence within C either has gain zero already or its symmetric difference with C does. Conversely a nonzero gain-zero cycle-space vector gives a proper second dependence because u≠0. Thus C is either a forest or it has just one ordinary cycle Q and γ(Q)=1. Multiple components in C are allowed.

## Aligning marked tree polynomials

Let H_G(D,S) use the **full** spanning-tree monomial x_T=∏_{e∈T}x_e for every spanning tree whose unique D-join J_T contains S. Sum over GF(2) or an extension. Multiply the unmarked-edge polynomial of the [rooted-join Pfaffian](../../djoin/pfaffian/README.md) by ∏_{e∈S}x_e when evaluating H. Return zero when G is disconnected or S contains an absent edge. For a desired gain b define

    L_G(D,S,b) = (1+b) H_G(D,S) + ∑_{a:γ_a=1} H_G(D,S∪{a}).

In a tree already passing the S test, the coefficient is 1+b+γ(J_T), precisely the indicator that γ(J_T)=b. This includes a∈S without duplicating its variable. Disjoint edge IDs remain distinct even on parallel edges.

The first polynomial L_G(u,R,1) detects forest witnesses: any forest extends to a spanning tree without changing its join, and the unique join of any accepted tree is itself a valid circuit.

## One-cycle terms

Compute the separate homogeneous polynomial

    U = ∑_{e:γ_e=1} x_e L_{G−e}(u△∂e, R−{e}, 0).

A contribution to x_K consists of a spanning tree of G−e plus e, giving a connected spanning unicycle K with unique ordinary cycle Q and e∈Q. Its candidate C is the unique (u△∂e)-join in K−e, augmented by e. It has boundary u, gain one, and contains R. A forest candidate is already a valid circuit. For a cyclic candidate, Q⊆C. In a fixed K, that same cyclic C occurs for exactly the edges e∈Q of gain one: deleting any such e leaves its unique required tree join, of gain zero, and the marker condition is satisfied. Its multiplicity modulo two is γ(Q). Thus cyclic candidates with an inadmissible even-gain cycle cancel, and a nonzero coefficient certifies some valid candidate.

Conversely, extend any genuine cyclic C to a connected spanning unicycle K by adding only edges joining distinct components, starting from (V,C). Its unique cycle Q has odd gain. K has just two u-joins, C and C△Q, since its cycle-space dimension is one. Their gains differ, so only C can contribute. Its multiplicity is odd. The two polynomials therefore decide this gain-one branch; no condition on the density of u or γ is imposed. Their degrees are n−1 and n respectively.

## Evaluation and recovery

Evaluate both polynomials at independently uniform edge values in a characteristic-two field of cardinality at least 2(n+2). A feasible instance has a nonzero polynomial of degree ≤n; Schwartz–Zippel gives false-negative probability at most one half per independent trial. A positive trial certifies feasibility. Each sample uses O((m+1)²) rooted-join evaluations with at most k+1 prescribed edges, hence 2^O(k) poly(n,m) time. The arithmetic remains valid for a graph with one vertex and for an unmarked or marked loop.

A successful evaluation recovers a support without another random choice. Keep the sampled point and impose edge-by-edge include/exclude requirements on full monomials of the successful polynomial. To evaluate under exclusions set their x coordinates to zero. For the current inclusion set I scale each x_e for e∈I by a common scalar z. Interpolate the coefficient of z^|I| from |I|+1 distinct points; it keeps exactly the required terms evaluated at the original x. Both polynomials are multilinear by construction. Try exclusion of the next edge; keep it when its restricted evaluation is nonzero and otherwise require inclusion. The previous nonzero value is the sum of the two disjoint branches. At most n edges can be included, so even one field of the stated size suffices. This uses polynomially many further evaluations.

For a recovered tree, solve its unique u-join by peeling leaves. For a recovered unicycle K, enumerate e∈Q of gain one and reconstruct the candidate on K−e. Check R containment, boundary, gain, and independence of all but one column of A[C] together with zero total column sum. A surviving coefficient guarantees at least one successful check. The net-gain-zero branch is a separate problem.

The independent check.py compares support-level enumeration with direct circuit minimality for all K₄ cases with nonzero even u, every γ, and up to three marked edges; 250 further connected multigraphs include loops and parallel edges. It checked 19,066 instances. The tree polynomial was nonzero in 4,942 and the unicycle polynomial in 6,709, with overlap possible. It directly confirmed 2,168 even-multiplicity groups of inadmissible cyclic candidates.
