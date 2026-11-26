# Zero-restriction certificates for order 401

Every nonlive variable has a private AND with a port-only off-path sibling accepting all its neighbor singletons. Tracing an accepting singleton backwards through that sibling reaches a strictly earlier nonempty producer owning the neighbor. Only a live owner can pass its singleton. Thus the nonlive point set and nonlive line set have no incidence. For their sizes $a,b$, centering their indicators and using the projective-plane matrix identity $MM^\top=qI+J$ gives $(q+1)^2ab\le q(N-a)(N-b)$.

**Residual weighted flow.** Let a zero restriction retain $n$ ordinary variables in an induced bipartite incidence graph of minimum degree at least $k\ge2$. Normalize the residual circuit. Every remaining variable is essential. The weighted-flow bound adapts to
$$
s'\ge 2n-1-\lfloor 2n/(k+1)\rfloor .
$$
Indeed any two same-side local variables specialize to OR by selecting one neighbor of each. A common neighbor is unnecessary. For opposite-side variables $x,z$, select a neighbor $p\ne x$ of $z$, then a neighbor of $x$ missing $p$ and distinct from $z$. Codegree one guarantees this: if $x$ lies on $z$ then $z$ is already excluded by $p$, otherwise $z$ was never a candidate. These OR specializations select at most two lines. They imply that every local branching ancestor is OR and adjacent variables cannot be in the same component. Distinct same-side stars remain distinguishable by degree and codegree. The private-AND and singleton-support arguments of the original weighted-flow proof therefore apply with weights capped at $k$. If $G$ counts variables other than the sole local variables of nonoutput components, and $e_0$ is the empty-producer excess, the selected siblings give $kG\le s'+1+(k-1)e_0$. Put $t=(s'-n+1)-(n-G)\ge e_0$ and $\delta=2n-1-s'=G-t$. Then $(k+1)\delta\le2n-t$.

**Counting simplified gates.** For a chosen set of eligible raw variables, let $Z(g)$ consist of variables whose individual deletion forces wire $g$ to zero with all other inputs one. At an input this is its eligible singleton or the empty set. At AND take the union, at OR the intersection. Put $A_g=Z(g_{\rm left})\cup Z(g_{\rm right})$. Every original gate with $A_g\cap D\ne\varnothing$ simplifies against a zero parent after deleting $D$. Let $R$ count these distinct gates. They count even if rewiring removes them earlier. One can also count actual zero parents under the simultaneous deletion, potentially increasing $R$.

**Independent deletions.** Delete raw variables of one or both polarities independently with probability $p$ and write $j$ for the number of eligible polarities. With $L=\lceil Nq/100\rceil$ and $\epsilon=jN\Pr[\operatorname{Bin}(q+1,p)>q+1-k]$, residual minimum degree at least $k$ fails with probability at most $\epsilon$. The expected saving after paying two gates per deleted variable is
$$
\mathbb E[R-2|D|]=\sum_g (1-(1-p)^{|A_g|})-2pjN .
$$
Write $T=L-4N+1+4N/(k+1)$. If $s<L$, on good restrictions the residual bound makes $R-2|D|+2|D|/(k+1)$ at most $T-1$. On any restriction this score is at most $s$. At order 401 the $T$ below is positive, so an expected saving above $T-2pjN/(k+1)+(L-1)\epsilon$ suffices. At $p=1/8$ this cutoff is below $3595.331$ for one polarity and $k=305$, and below $3468.912$ for both polarities and $k=304$.

**Pencil deletions.** Choose a uniform center point $O$ and choose $h$ distinct uniform lines of its pencil, with $1\le h\le q-1$. Delete those lines and their points other than $O$. This deletes exactly $d=h(q+1)$ variables. The center loses $h$ lines, and every retained line outside the pencil loses $h$ distinct points. Each other retained point and each retained pencil line keeps all its neighbors. Thus the residual degree is at least $k=q+1-h$ on every outcome.

Partition $A_g$ by point and line variables. For fixed $O$, let $v_O(g)$ be the number of distinct pencil lines obtained by joining $O$ to the points in $A_g$ other than $O$, together with the pencil lines in $A_g$. The conditional probability of counting $g$ is
$$
1-\binom{q+1-v_O(g)}h\big/\binom{q+1}h ,
$$
with a zero numerator when fewer than $h$ lines can be chosen. Averaging over $O$ and summing over $g$ gives $\mathbb E[R]$ with no independence assumptions among gates. The dual construction interchanges the two polarities.

For $q=401$ and $h=50$, $N=161203$, $L=646425$, $d=20100$, $n=302306$, $k=352$, and $\lfloor2n/(k+1)\rfloor=1712$. The residual circuit has at least $602899$ gates. Hence a saving $R-2d\ge3326$ suffices. By integrality, $\mathbb E[R]>43525$ already suffices. This cutoff is lower than the one-sided independent-deletion cutoff at a comparable mean number of deletions, but the gate weights are incidence-dependent and the expected savings need not be ordered.

These are conditional tests on actual gate profiles. They do not establish that every circuit of the proposed size passes a test.

**Mixed pencil constants.** Also delete $O$. All points on the selected lines are then zero, so each of the $h$ selected line variables can instead be fixed freely to zero or one. An old incidence on those lines is impossible. If $h\le q-2$, the original sparse promise still covers the residual tests with at most two new lines. An unselected pencil line loses just the center, and the residual minimum degree is still at least $q+1-h$. The additional deleted variable increases the number of gate removals needed at the numerical setting from 43,526 to 43,528. A gate certainly simplifies whenever either parent becomes a constant under this mixed restriction. To identify all constant parents exactly, evaluate once with every free variable zero and once with every free variable one. Monotonicity implies a gate is constant precisely when its two evaluations agree. This includes cascades of ones through OR gates and cascades of zeros through AND gates.
