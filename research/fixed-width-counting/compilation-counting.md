# Counting obstruction for pointwise bounded-width compilation

Fix n distinguished input bits. For any m-element subset S of the Boolean cube, the conjunction of one full-width clause per s∈S, forbidding s, represents the complement of S. Distinct S give distinct functions, so this family has exactly binom(2^n,m) functions with precisely m clauses. Put H=log₂ binom(2^n,m). For m≤2^(n−1), H≥m(n−log₂m), by the elementary product bound binom(L,m)≥(L/m)^m. In particular H is asymptotic to nm for m polynomial in n.

A width-k CNF using at most N named Boolean variables has at most

$$
 2^{B(N,k)},\qquad B(N,k)=\sum_{j=0}^{\min(k,N)}2^j\binom Nj
$$

semantic possibilities before projection: normalize clauses by removing tautologies, duplicate literals and duplicate clauses. Extra names can be drawn from a pool; for an upper bound on distinct projected functions, unused auxiliary variables cause no problem. With the original n variables distinguished in fixed order, existential projection of each CNF onto them produces a single Boolean function. So if H>B(N,k), some source formulas admit no such projection, even with unlimited output clauses, unbounded compilation time and arbitrary nonuniform choices. In fact a uniformly random S is representable with probability at most 2^(B−H). Unique extension for every satisfying input is a stronger condition and obeys the same impossibility. If the compiler chooses an injective ordered list of n input coordinates, one can rename variables to the fixed convention; arbitrary semantic decoders are outside this model.

For fixed k≥1, B(N,k)≤O_k(N^k). Thus some inputs with m=n^c require N=Ω_k(n^{(c+1)/k}) whenever c>0 is fixed. In particular for c>k−1 no N=O(n log^a n) bound works for any fixed a. For c=k−1 and logarithmic auxiliary overhead this counting argument is inconclusive. For any fixed k, one can choose a polynomial density exponent c that rules it out, but the argument does not rule out letting fixed k depend on c.

For growing k≤N, B(N,k)≤(2eN/k)^k: use the elementary binomial tail bound with the factor 2^j bounded by 2^k. A sufficient obstruction is consequently

$$
 k\log_2(2eN/k)<\log_2(m(n-\log_2m)).
$$

Conversely B(N,k)≥2^k(N/k)^k by keeping just the k term. These bounds locate the transition of this counting test at k log₂(N/k)+O(k)≈log₂ H when k=o(N). If m=2^{n^β} for 0<β<1 and N=n log^{O(1)} n, every k≤(1−ε)n^β/((1−β)log₂ n) fails for fixed ε>0 and all sufficiently large n. Widths above the transition evade this particular pigeonhole argument without implying a compiler exists.

Every member of the source family has the very same answer to scalar exact counting, 2^n−m, and is satisfiable whenever m<2^n. Thus this lower bound addresses neither decision-preserving reductions nor count-only reductions. In fact any specified integer C∈[0,2^n] is the number of satisfying assignments of a width-three CNF with O(n) variables and clauses: the n input bits represent an integer x, and a linear-size deterministic comparator circuit tests x<C with unique auxiliary gate values. Handle C=2^n by the unconstrained cube. An efficient count-only compiler may still have a difficult computational task, but counting inequivalent functions cannot prove that.

Width two has a stronger absolute obstruction. Eliminating an existential variable from a 2-CNF adds at most binary resolvents, so every existential projection of a 2-CNF is again definable by a 2-CNF. For 0<m<2^(n−2) the cube minus m points is proper and cannot satisfy any non-tautological clause of width at most two on every remaining point: the falsifying subcube of such a clause has at least 2^(n−2) points. Thus no width-two pointwise projection exists for these functions at any auxiliary-variable budget.
