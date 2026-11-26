# Clause space times logarithmic length in parity resolution

Let a refutation begin with an empty configuration, download input clauses one at a time, add sound semantic consequences of any number of retained lines, erase retained lines, and end retaining the contradiction. Every retained line is a disjunction of affine GF(2) equations on the original variables. Let s be its maximum number of simultaneous lines, and L its number of transitions. For the bounded-occurrence [guarded family](README.md) with N variables,

$$s\log(2L)=\Omega(\sqrt N).$$

Thus every polynomial-length refutation uses Ω(√N/log N) clause space. This bound permits arbitrary line widths, arbitrary semantic inference fan-in, erasure and recomputation.

## Testing a configuration

For a fixed distributed assignment write B(t)=1 when some retained line at time t is false. For each line i, falsity requires simultaneous violations of its equations. On the split assignment these are a single string equality uᵢ(x)=vᵢ(y), with the complements and constant terms placed on Bob's side. The two parties form sets of strings (i,uᵢ) and (i,vᵢ), one item per retained line. Their intersection is nonempty exactly when B(t)=1. Sparse set disjointness gives a public-coin O(s)-bit test with any desired fixed constant error, independent of the universe size. Public randomness and local computation are unrestricted. [Håstad and Wigderson, Theorem 1.3](https://toc1234.cs.uchicago.edu/articles/v003a011/)

## Locating an input

Pad the trace by repeating its last configuration until the number of transitions is a power of two. Its dyadic interval tree has height h=⌈log₂ L⌉. An interval [a,b] is valid when its endpoints have B(a)=0 and B(b)=1. The root is valid. Every valid interval of length at least two has exactly one valid child, determined by B at the midpoint. This assertion permits arbitrary behavior of B elsewhere. At a valid unit interval the transition must download a false input. Sound inference from jointly true retained lines, erasure and padding cannot create the first false line in a configuration.

Start at the root. At each internal interval estimate both endpoints and its midpoint with fresh public coins and joint error at most 1/10. If the estimates indicate validity descend to the indicated child. Otherwise ascend, staying at the root if necessary. At a unit interval check the actual input for that transition exactly if it is a download and return it if false. Otherwise ascend. This verification costs O(1) bits because the inputs are bounded-arity clauses. A returned answer is always correct.

For the current path, give each nonroot valid interval weight +1 and each invalid interval weight −1. Its sum is at most h. Subject to nontermination, each accurate step increases the sum by one and every step decreases it by at most one. On the event of no answer after T=10(h+1) steps the number of inaccurate steps must be at least (T−h)/2. Fresh randomness bounds their expected number by T/10 (count errors after termination as zero). Markov's inequality bounds the failure probability by 2T/[10(T−h)]<1/3. Total communication is O(s log(2L)). By the matching-versus-odd-coloring reduction every bounded-error search needs Ω(√N) bits.

The same argument applies to any bounded-arity CNF on a fixed variable partition, replacing Ω(√N) by the randomized communication complexity of its falsified-clause search. It concerns the storage of proofs over original-variable parity clauses. A solver with unrestricted auxiliary predicates or an unrestricted decision algorithm need not produce such a trace. An independent [depth argument](../audit/dag-depth.md) gives depth Ω(√N) for binary semantic inferences, even with unlimited clause space.

## Mixed quadratic inferences

More generally, allow clauses of arbitrary many equations, each having the form f(z)+g(q)+zᵀMq=c over GF(2). Functions f,g may be arbitrary on their respective parties. For each configuration let U span the columns of *all* mixed coefficient matrices in its live equations. Use b for the maximum of dim U over time. Testing a chosen configuration costs O(b+s) bits. Its public basis u₁,…,u_d has d≤b. Alice transmits each zᵀuⱼ. Bob can consequently reconstruct zᵀM locally for every matrix in the configuration and evaluate all the remaining mixed terms using q. Each resulting equation splits into two local bits, so the tagged-equality argument applies verbatim. Semantic inferences among these lines therefore satisfy

$$(s+b)\log(2L)=\Omega(\sqrt N).$$

The basis can be chosen on the cheaper of the two sides anew for each configuration, using row spaces on Bob's side. In particular, a degree-two polynomial-calculus proof is a trace of singleton-equation clauses. With s=O(1) and polynomial L some live polynomial must have mixed coefficient matrix of rank Ω(√N/log N), by subadditivity of dimension. A concrete polynomial-length constant-space proof exists by retaining a running sum of the native guards, downloading the next guard, adding and erasing. If starting from canonical CNF polynomial axioms instead, literal products may exceed degree two, so the constant-degree-two upper bound here concerns the native axioms.
