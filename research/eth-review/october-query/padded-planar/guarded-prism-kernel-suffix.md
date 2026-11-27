# Exact kernel streaming on the guarded prism leaf

Use the declared variables, row semantics and fixed dense dispatcher of [the guarded-circulant construction](guarded-circulant-positive-handoff.md). Choose the connected simple cubic base graph to be a prism on $v=2l$ vertices, $l\ge4$. The dense fillers ensure the original source takes its hash route. Only its guard-true sparsification leaf is analyzed here. This leaf has one guard unit and one positive clause $(x_i\lor x_j\lor z_e)$ per primal edge. It retains $n=1+v+3v/2$ declared bits and has $q=1+3v/2$ physical clause-violation coordinates. No spin, gate, or guard pin is required by the suffix algorithm.

## Evaluating one violation profile

For a word $w$ let $h(w)$ count the physical assignments with exactly that clause-violation word. The guard contributes one choice, $g=1-w_g$, or zero if it conflicts with an imposed pin. For an edge with endpoint bits $a,b$, its two-spin factor is

$$
K_e(a,b)=\sum_{z\in\{0,1\}\text{ consistent with pins}}
 [\,(1-a)(1-b)(1-z)=w_e\,].
$$

Restrict each base spin to its allowed values as well. Contradictory pins give zero. Multiplying the factors and summing the base spins gives $h(w)$, including multiplicities of unpinned gate assignments. In particular an unpinned edge at $w_e=0$ contributes two when an endpoint is one and one otherwise. Treating every feasible profile as having weight one would give incorrect scores.

Write the two spins at column $i$ as a state $s_i$ of size four. Its unary weight is the rung factor times endpoint-pin indicators. Its transition to $s_{i+1}$ is the product of the two rail factors. Fix the initial state in four ways, propagate a four-entry integer vector down the ladder, multiply by the closing two rail factors and sum. This visits $O(l)$ constant-size tables. Intermediate integers have $O(n)$ bits: each nonnegative term counts choices of a subset of the physical spins and gates, or is bounded by $4^l2^{3v/2}$ directly. Thus evaluation is polynomial bit time and space, also with arbitrary consistent raw coordinate pins. Pins only modify this evaluator; the trajectory guarantee below is for the unpinned source.

The prism need not come with a layout. In this leaf the unique unit identifies the guard, each gate appears once, and the degree-three variables are the base spins. Validate the entire clause list, all roles and the simple cubic graph. Try every ordered 4-cycle as a seed for two consecutive ordered rungs. At each end of the current rung the third neighbor, after excluding its mate and its previous rail neighbor, uniquely specifies the next spin. Check the rungs, distinctness until closure, both closing rail edges and equality of the entire graph with the reconstructed prism. Trying the actual two-rung seed succeeds; an alternative seed is harmless if its reconstruction passes. Even a brute enumeration of ordered vertex quadruples followed by traversal costs polynomial time.

## Replaying the native suffix

Take the initial Tanner checks and successive selected rows in their original $q$-column representation. At a prefix of rank $r$, compute a binary basis of its kernel by polynomial-time elimination. For each actual ordered source trial of length $P$, combine repeated coordinates modulo two to give a row $c$. Its score is the exact integer

$$
\sum_{w\in\ker A\, :\, c\cdot w=0}h(w).
$$

Stream binary combinations of the kernel basis and compute the factors above as needed. This uses $2^{q-r}\operatorname{poly}(n,P)$ bit time per candidate and polynomial space. The partial sums are at most $2^n$. Retain the first minimum in the source's chosen trial order, append it, and repeat. The same evaluator gives the final selected-system count. All candidates, including redundant rows, the zero row and repeated ordered representations, are priced. No sampled scores or training data enter.

With $\lambda=\lceil\log_2 n\rceil$, the source's width-three schedule gives $B=\Theta(\lambda(\log\lambda)^2)$ and $P=20000B^2(\lfloor\log_2 q\rfloor+1)^2=\Theta(\lambda^4(\log\lambda)^4)$. Hence $\log_2((2q)^P)=O(\lambda^5(\log\lambda)^4)$. Upon reaching deficiency $d_*=\lfloor n/\lambda\rfloor$, the required residual deficiency never increases, even after full rank. Counting every remaining round up to the original total of $3n$, not just the rank-increasing rounds, costs

$$
(3n+1)(2q)^P2^{d_*}\operatorname{poly}(n,P)
=2^{O(n/\log n)}\operatorname{poly}(n).
$$

On this unpinned leaf every violation profile is realizable and every minimizing choice increases rank until rank $q$, by the singleton-trial argument in the linked construction. The algorithm can therefore reach the threshold by running the native procedure from the original input and inspecting the selected prefix; its initial rank is $o(q)$. **The prefix, initial construction, and other sparsification child are separately charged.** The displayed suffix clock is not a clock for the entire original run. At full rank the kernel is just zero, but $h(0)$ still requires evaluation if the count has not already been retained.

At the threshold there are exactly $2^{d_*}-1$ distinct surviving nonzero patterns. For a uniform kernel word, each base vertex has all three incident edge coordinates zero with probability at least $1/8$. Omitting the zero word reduces the unconditioned expectation of their number by at most $v/2^{d_*}$. For $d_*\ge4$ some nonzero word therefore has at least $v/16$ such vertices. Fix the guard and gates to $1-w_g$ and $1-w_e$; fix both endpoints of violated edges to zero. All remaining base spins can vary freely without changing the violation vector, so that word has weight at least $2^{v/16}$.

For an arbitrary supplied cubic graph the same kernel formula works, but a direct spin sum costs $2^v\operatorname{poly}(n)$ per word. A supplied recursive balanced separator of size $O(\sqrt u)$ on every $u$-vertex remaining piece gives $2^{O(\sqrt v)}\operatorname{poly}(n)$ time per profile and polynomial space by streaming separator assignments; discovery must be priced if the layout is not supplied. These special scalar evaluations impose no lower bound on other ways to count models or to evaluate discarded trials.
