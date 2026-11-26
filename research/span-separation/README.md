# Two linear matroids suffice for one target and one excluded vector

Let $E$ be an indexed family of binary columns and let $u,w$ be terminal vectors. Seek $X\subseteq E$ with $u\in\operatorname{span}X$ and $w\notin\operatorname{span}X$. This includes the formulation $w\notin\langle u\rangle+\operatorname{span}X$, since feasible $X$ already span $u$.

When $u=0$, the empty set works exactly when $w\ne0$. Otherwise reject $w=0$ and $w=u$. In the remaining cases put $V=\operatorname{span}(E\cup\{u,w\})$ and $d=\dim V$. On the common ground set of indices of $E$ represent two linear matroids by the quotient maps
$$
E\longrightarrow V/\langle w\rangle,\qquad
E\longrightarrow V/\langle w+u\rangle.
$$
A witness exists exactly when these matroids have a common independent set of size $d-1$. Deterministic linear matroid intersection with Gaussian-elimination independence oracles therefore finds a witness or decides infeasibility in polynomial time.

For necessity, take an independent basis for the span of any witness $X$. Together with $w$ it is independent. Extend this set to a basis of $V$ using columns of $E$, which is possible because $u\in\operatorname{span}X$. Removing $w$ gives a hyperplane basis from $E$. Its span contains $u$ and excludes $w$, so it excludes $u+w$ as well. It remains independent in both quotients.

For sufficiency a common independent set of size $d-1$ spans a hyperplane of $V$ excluding both $w$ and $u+w$. Its nonzero binary annihilating functional has value one on both excluded vectors, hence value zero on their sum $u$. The set itself is a witness. The use of a binary field matters in this implication.

The independent checker rank_one_check.py compares the criterion against direct enumeration for all 5,376 instances consisting of a subset of the seven nonzero columns in dimension three and an ordered pair of distinct nonzero terminals. It verifies the criterion, without implementing the general matroid-intersection algorithm.

For the supplied signed-graph representation, the [odd-cycle method](even-cycle.md) handles terminal spaces containing the pure sign direction with the stated dependence on their dimension.
