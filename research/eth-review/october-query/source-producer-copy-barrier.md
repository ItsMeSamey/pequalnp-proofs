# Raw COPY cost in the October final-query producer layout

For infinitely many declared variable counts $n$, the final parity query in the October construction forces native scale $s=\Omega_C(n\sqrt d)$ for a compiler that assigns each surviving violation monomial to exactly one producer, shares physical variables by raw COPY ports, and transmits each producer’s losslessly recoverable contribution to the final syndrome. Here $d=\Theta((\log n)^{1/4})$, the native graph has at most $Cs$ wires, and the degree of every vertex is at most $\lceil s^{9/10}\rceil$.

## Source family and exactness

Use the explicit LPS base in [the final union-shell construction](final-union-shell-obstruction.md), with $N=n/2$ base vertices, degree $d$, and one fresh third vertex on each clause triple selected from a pool of $N$ fresh variables. The base graph is simple, and the third-vertex allocation gives a linear 3-uniform hypergraph with maximum variable degree at most $2d$. “Fresh” describes the pool relative to the base vertices. Individual pool vertices can serve several triples. The all-negative 3-CNF has $nd/4$ clauses, takes the October dense branch and remains a single sparsification leaf. The final Tanner-plus-greedy rows are homogeneous binary sums of the violation cubics. Their common zeros coincide pointwise with the models of the CNF: every model survives each check by construction, and the final count equals the model count.

Follow the all-zero branch of the source’s heavy-variable fixing; further fixing $o(n)$ physical variables to zero is also allowed. Fixing deletes at most $2d$ triples per variable, so $m'=\Omega(nd)$ triples survive. These are the original squarefree cubics indexed by their distinct vertex triples. Each appears in a final row, since setting precisely its three coordinates to one realizes it as the sole violation. The incidence and pointwise exactness properties hold after this restriction. The explicit base uses the LPS construction and primes in a fixed progression as specified in the [source family note](final-query-period-obstruction.md), with the degree schedule above. The proof uses its one-sided spectral estimate. It does not require a random-graph small-set degeneracy assertion.

## Local information forced at one producer

Write $E_h$ for the triples assigned to producer $h$, and $A$ for the binary matrix of final polynomial coefficients, one column per surviving triple. The intersection graph of all surviving triples has maximum degree at most $6d$. Its square has maximum degree at most $36d^2+6d$. Greedy selection from any $E'\subseteq E_h$ therefore yields a set $I$ of size at least $|E'|/(36d^2+6d+1)$, with chosen triples pairwise at distance greater than two in the full intersection graph. An outside triple contained in their union would have to meet at least two of them, since the triples are distinct and have equal size. It would create a length-two path. Thus every subset of $I$ is realizable as the exact set of violations by setting precisely its vertices to one.

The columns $A_I$ are independent. A nonempty subset whose columns sum to zero would produce an assignment passing every final check despite violating a clause. For the linear check-column compiler, the sum of output ranks across any partition of the rows dominates the rank on $I$. Thus $|E_h|=O(d^2 a_h)$, where $a_h$ is the producer’s physical degree.

The same inequality holds if a producer may choose a nonlinear binary encoding adapted to its shared input values, provided its transmitted words and the shared inputs determine its complete local syndrome. Let $q_h$ denote its number of distinct shared physical inputs and $b_h$ its total transmitted bits. Discard from $E_h$ all triples meeting a shared input. At most $2d q_h$ disappear. Apply the same greedy selection to the remaining private triples. Fix all shared inputs to zero. The $2^{|I|}$ selections just constructed give $2^{|I|}$ different local syndromes $A_I y$ at this same shared setting. A fixed binary interface that permits syndrome recovery must therefore have $b_h\ge |I|$. In particular

\[
 |E_h|\le 2d q_h+(36d^2+6d+1)b_h=O(d^2a_h),
 \qquad a_h\ge q_h+b_h .
\]

The hypothesis is recovery of the whole local syndrome. Exact pointwise acceptance by an AND of local flags does not imply syndrome recovery: a flag may merge many distinct nonzero syndromes. Neither that acceptance-only implementation nor a compiler that only preserves the final scalar is covered by this information argument.

## Global wire bound

It suffices to consider $s<n\sqrt d$. Each producer touches at most $3|E_h|=O(d^2(1+s^{9/10}))=o(n^{0.95})$ triple endpoints. For $X_h$ the base endpoints it touches, the upper Rayleigh estimate gives

\[
 |E_h|\le e_G(X_h)
 \le \tfrac12\bigl(d|X_h|^2/N+2\sqrt{d-1}|X_h|\bigr)
 \le 2\sqrt d\,|X_h|
\]

for all sufficiently large $n$. This uses one base edge per triple; a bipartite eigenvalue $-d$ can only decrease the upper Rayleigh quotient. Summing over producers gives $\sum_h|X_h|\ge m'/(2\sqrt d)=\Omega(n\sqrt d)$. At most $n$ of these mentions belong to variables private to one producer. Each remaining mention requires a separate producer-side raw COPY port, and each such port accounts for a distinct wire in this bipartite implementation. Hence $Cs\ge\Omega(n\sqrt d)-n$, proving the claim. The other regime $s\ge n\sqrt d$ already satisfies it.

This lower bound concerns the scale required by the specified native implementation. It applies to arbitrary assignment of monomials and partition of tests, and to row operations preserving the full polynomial row space. It gives no lower bound for changing the Boolean input coordinates, replacing local syndromes with acceptance-only flags, repartitioning the computation into other factors, or directly computing the scalar.
