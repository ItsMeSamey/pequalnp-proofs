# Row reuse from support minrank

Let $P,V$ be finite sets and let $A_p,K_p\subseteq V$ for each $p\in P$. Suppose that $|A_p\cap A_t|\le 1$ whenever $p\ne t$. Write $L=\{p:K_p\subseteq A_p,\ |K_p|\ge2\}$. Over a field $F$, the support minrank of $K$ is the least rank of a matrix $M\in F^{P\times V}$ with $M_{pv}\ne0$ exactly when $v\in K_p$.

**Theorem.** If $K$ has support minrank $r$ over $F$, then $|L|\le \binom{r+1}{2}$.

**Proof.** Restrict a witnessing matrix to rows in $L$, and choose a basis $b_1,\ldots,b_d$ of its column space, where $d\le r$. For each $p\in L$, choose distinct $v,w\in K_p$. The coordinatewise product of columns $v,w$ is nonzero in row $p$. A second nonzero entry in row $t$ would put both $v,w$ in $A_p\cap A_t$. Thus the selected products are nonzero multiples of distinct coordinate vectors and are linearly independent. By bilinearity and commutativity, all column products belong to the span of $b_i\odot b_j$ with $1\le i\le j\le d$. This gives $|L|\le d(d+1)/2\le r(r+1)/2$. ∎

The proof works in every characteristic. A cover by $k$ rectangles gives support minrank at most $k$ over the rationals by summing the rectangles' indicator matrices. Over a finite field this sum can cancel on overlaps. The theorem only needs one witnessing field, which may be chosen separately for each gate.

**Sharpness under the overlap hypothesis.** For $r\ge1$, take the rows to be the edges of the complete graph on $r+1$ vertices and the columns to be its vertices. Set $A_p=K_p$ equal to the two endpoints of edge $p$. Distinct rows share at most one vertex, and all $\binom{r+1}{2}$ rows qualify. Over $\mathbb F_2$, the unsigned incidence matrix maps a vertex vector $x$ to its endpoint sums $x_u+x_v$. Its kernel consists precisely of constant vectors, so its rank is $r$. Over any other field, orient the edges and use endpoint differences $x_u-x_v$ to obtain the same support and the same kernel. The theorem excludes smaller rank over every field. This establishes sharpness for the abstract row bound.

**Scalar circuit consequence.** For a projective plane of order $q$ with $N=q^2+q+1$ points, the local gate count provides at least $Nq$ qualifying point–gate pairs. If at most $h$ of the $s$ scalar gates lack a support-minrank witness of rank at most $r$, then
$$
 Nq\le Nh+s\binom{r+1}{2}.
$$
In particular, $r\le9$ and $2h\le q$ imply $Nq\le90s$. The argument leaves open how often high minrank occurs in the original circuit.
