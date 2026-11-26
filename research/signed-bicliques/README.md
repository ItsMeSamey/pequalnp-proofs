# Exact counting across signed biclique interfaces

Let L be full explicit input length including the supplied decomposition. All clause widths k are bounded by a common fixed constant at least two. The quantitative bounds assume the October 25 OpenAI manuscript. No priority claim is made.

## Flat composition

Partition variables into blocks with local k-CNFs F_i on b_i variables and O(b_i) clauses each. All other clauses are supplied in edge groups of a quotient multigraph. An edge ij with signed literal sets P at i and Q at j represents every binary clause (p OR q) with p in P and q in Q. Groups may overlap; comparing expanded clause sets verifies the supplied decomposition in polynomial time. Distinct literal signs and overlapping ports within each block are allowed.

Let b be the largest block, d the maximum quotient degree, and w the maximum number of edges crossing a prefix of a supplied vertex order. Exact counting takes

    poly(L) [2^{O(b/sqrt(log b))+d} + 2^{w+d}]

bit operations. Thus d,w=O(log L) and b=O(log L sqrt(log log L)) suffice for polynomial time. Drop the density assumption using b log log b/sqrt(log b) instead of b/sqrt(log b). Constants depend on k and the density bound.

The bit of a port equals 1 if all its signed literals hold. An edge group holds iff at least one endpoint bit is 1. For each subset S of ports at a block, compute M(S), the number of models of its local formula that pin every literal in S's ports. This is one #kSAT call. Normalizing constraints adds at most one unit per original variable; conflicting pins give zero. Keep original variable count to preserve bounded density. If H(T) counts models having true port set exactly T, then M(S) is the sum of H(T) over supersets T of S. Upper-set Möbius inversion gives the full H table in O(d 2^d) integer operations. Along the order, store one bit per crossing edge, recording its processed endpoint's value. Loop over patterns at a new vertex, validate closing edges, insert opening bits, multiply by H(T), and sum by resulting state. Induction on the processed prefix proves the answer. Counts have O(L) bits and intermediate inversion entries count assignments with some required and some forbidden port bits.

For a separating family take a path of T blocks with b=floor(log T (log log T)^{1/4}) variables each, arbitrary sparse local factors, and a full positive port at both sides of each edge. Here log L=Theta(log T). Removing O(log L) variables leaves every block nonempty and the entire remaining primal graph connected. The primal graph contains K_{b,b}, so its treewidth is at least b. The exhaustive local 2^b and ordinary 2^{primal treewidth} guarantees are superpolynomial; the flat algorithm above is polynomial. These statements concern the guarantees of the named methods and do not assert lower bounds against other structural algorithms.

## Recursive composition

In a supplied binary hierarchy, leaves are arbitrary sparse local fixed-width CNFs on disjoint variables. Each internal node joins its children by a signed biclique of binary clauses, with ports A and B. Let Z(P) denote conditional count under pins P, split into P_l and P_r. Set u=Z_l(P_l), u'=Z_l(P_l union A), v=Z_r(P_r), v'=Z_r(P_r union B). Inclusion-exclusion gives

    Z(P) = u'v + uv' - u'v'.

Each of these four operands is evaluated once per call. At height h this costs O(4^h) calls. Passing normalized pins is polynomial in L. Thus h=O(log L) and b=O(log L sqrt(log log L)) yield polynomial exact counting. A balanced split halves the number of equal-sized leaves at each step.

Take a balanced hierarchy with T leaves of b variables each as in the flat example. At every node let each port contain one independently chosen signed literal on each variable in its child. Every pair in different leaves occurs in a binary clause generated at its least common ancestor. The flat quotient on these leaves is therefore a clique. No reblocking into blocks of O(b) variables restores logarithmic quotient degree: select one representative per original leaf. These T representatives form a clique in the primal graph and must occupy at least Omega(T/b) new blocks. The flat quotient on those blocks contains a clique. This proves a separation of these two explicit sufficient conditions. Other methods could count these same instances; no lower bound against all algorithms follows.

An arbitrary-depth variant computes each unrestricted child count once from the bottom up. If each port pins all but at most q variables of its child, compute the pinned operands by simplifying the child's explicit formula and applying the general #kSAT theorem to the remaining variables. Account for unused free variables if the implementation removes them. Each child description has length at most L. For q=O(log L sqrt(log log L)/log log log L), the reduced counts take polynomial time, independently of the hierarchy height. An unbalanced comb with full or near-full ports is included. Its pinned residual need not have bounded density, which explains the log log log L denominator.

## Verification and prior context

The adjacent check.py tests the inversion and path count against direct exhaustive counting on 200 seeded signed paths and tests the recursive identity against exhaustive counting on 200 signed hierarchies. Numerical checks cover the identities; the asymptotic local improvement uses the manuscript. The associated Lean formalization has a weaker exponent.

Sum-product tensor composition and structural model counting are established techniques. This derivation uses the manuscript's faster local factor evaluation. It supplies no general CNF decomposition or evidence of priority.

* [OpenAI quantitative reduction](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex)
* [Scope of formalization](https://github.com/openai/math/blob/main/lean/docs/378.md)
* [Kschischang, Frey and Loeliger, Factor graphs and the sum-product algorithm](https://www.isiweb.ee.ethz.ch/papers/arch/aloe-2001-1.pdf)
* [Model Counting for CNF Formulas of Bounded Modular Treewidth](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2013.55)
* [Model Counting for Formulas of Bounded Clique-Width](https://arxiv.org/abs/1409.8464)
* [Efficient Contraction of Large Tensor Networks for Weighted Model Counting through Graph Decompositions](https://arxiv.org/abs/1908.04381)

[Expanding incidence graphs](expander.md) give a parsimonious, linear-combinatorial-size encoding of arbitrary 3-CNF with three distinct variables per clause and at most 23 occurrences per variable. The graphic core also gives an exact cut-rank formula and a counting algorithm parameterized by the variables touched by nonlinear defects.
