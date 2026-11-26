# P versus NP research checkpoints

The files on this branch contain partial results in both directions. The full P versus NP problem and the general versions of the circuit steps remain open in this work.

| Direction | Checked result | Outstanding question |
| --- | --- | --- |
| SAT algorithms | A matching between clauses and distinct variables certifies satisfiability. Given a core of variables and a matching covering every other clause outside that core, Lean proves that solving the internal clauses suffices. | The matching-based algorithm can require exponentially many assignments. See the [solver, tests, and counterexamples](hall-solver/README.md). |
| Incidence circuits, L-meta-2794 | For a projective plane with N points and N lines satisfying the posted assumptions, every allowed circuit passing the tests has at least 2N+q gates. The adaptive deletion proof strengthens the result and establishes the requested bound for orders 101 through 288. On every sparse right input the circuit must compute incidence exactly. | The target asks for at least Nq/100 gates for every order q greater than 100. The verified inequalities leave orders above 288 open. |
| Finite circuit synthesis, L-meta-8032 | Lean checks that the 24 listed masks are exactly the maximal independent masks. Passing the 16 positive and 24 negative tests therefore determines any monotone output on all 2,048 inputs. | The step asks to rule out a circuit with at most 21 gates and at least three specified dirty AND gates. The truth-table equivalence does not bound the number of gates. |
| General circuit counting | When the number of circuit descriptions is smaller than the number of Boolean truth tables, every evaluator misses a truth table. | Counting does not put a hard language in NP. |

From a checkout with the pinned Lean and Mathlib dependencies installed, run `research/check.sh` to check the formal statements and the executable SAT tests. To reuse a separate checkout with the same pinned dependencies, set `PNP_LAKE_DIR` to its `lean/` directory.

The bounded-occurrence SAT case formalizes a classical result. [Tovey's paper](https://doi.org/10.1016/0166-218X(84)90081-7)

[AdaptiveIncidence.lower](../lean/Research/AdaptiveIncidence.lean) proves the 101–288 range directly from the L-meta-2794 assumptions. It constructs an adaptive deletion sequence, verifies the savings of each rewiring, and bounds how many vertices lose their neighbors. The [deletion notes](incidence-deletion.md) give the mathematical argument.

[HallLeastCore](../lean/Research/HallLeastCore.lean) proves that alternating reachability finds the least matching core under the matching stopping condition. The [maximum-deficiency-one solver](hall-solver/DEFICIENCY_ONE.md) handles formulas where a maximum incidence matching misses at most one normalized clause. The [pivot proof](../lean/Research/DeficiencyOnePivot.lean) verifies a matching exchange in the known polynomial-time algorithm for this case. The executable passed exhaustive tests on two variables and 5,000 random comparisons. [Szeider's paper](https://doi.org/10.1016/j.jcss.2004.04.009)

For L-meta-5882, [PlaneSampleRectangleCost](../lean/Research/PlaneSampleRectangleCost.lean) proves that every unshared OR of bicliques satisfying the sample promise needs at least 64 gates. Just thirteen translations of one negative mask rule out all non-incidence cross pairs. The 63-gate search permits other circuit structures and shared computations.

The [21-gate candidate](../lean/Research/EdgeCandidate.lean) for the separate L-meta-8032 graph passes 39 of 40 tests and has three dirty AND gates. It misses edge (1, 4).

[PlaneSixLines](../lean/Research/PlaneSixLines.lean) constructs the 29-gate first part of a proposed L-meta-5882 reduction. It processes six lines and exposes twelve point-pair ORs, six larger ORs, and the aggregate output for reuse. The remaining part must use at most 34 gates to classify all required samples.

[Violation moments](violation-moments/README.md) constructs bounded-width SAT and UNSAT formulas whose aggregate clause-violation moments agree to arbitrarily high order.

The [simultaneous incidence bound](incidence-simultaneous.md) proves Nq gates for one output per point and gives a conditional scalar bound in terms of gate rectangle covers.

[Affine projection](rank-projection/README.md) gives a polynomial-time compiler when each residual clause depends on at most one independent hidden linear form over GF(2). Allowing two such forms permits a direct reduction from 3-SAT.

[Compatible partitions](fiber-solver/findings.md) gives a witness-producing solver for binary tables whose endpoint partitions agree and shows what happens when adjacent tables impose different partitions.

[Guarded affine projection](guarded-affine/README.md) compiles a family of existential formulas with b terminal clauses in polynomial time for fixed b. Computing n-bit inner product in this model takes exactly n+1 terminal clauses. The proof also identifies the size of the smallest cover of its accepting inputs by affine flats.

[A polynomial-calculus counterexample](polynomial-calculus/README.md) gives 22 Boolean variables, one quadratic constraint per pivot and one affine parity marker. Its refutation degree over GF(2) is exactly four. The lower-bound certificate excludes every degree-three derivation, and the supplied upper-bound trace can be replayed directly.

[Compressed functional pigeonhole systems](guarded-pigeonhole/README.md) have hidden rank deficiency one and require linear polynomial-calculus refutation degree over GF(2). A polynomial-size linear program refutes this same family directly from the input coefficient masks.

[Signed biclique composition](signed-bicliques/README.md) applies the October manuscript’s exact counting bounds to supplied decompositions of fixed-width CNF. It gives separate flat, balanced-recursive, and near-full-port algorithms.

[Fixed gate obstructions](seed-obstructions/README.md) exclude four specified subprograms from any 34-gate completion of L-meta-18968. The certificates use disjoint positive–negative difference sets on the raw statement.

[Two-leaf incidence witnesses](incidence-witnesses/two-leaf.md) bound scalar gates by the number of edges admitting a two-leaf accepting parse. The accompanying notes quantify gate reuse by support minrank and rectangle covers.

[Low-rank affine conditioning](affine-backdoor/README.md) searches for an optimal subspace that brings each clause to hidden rank at most one. [Signed cut counting](signed-cuts/README.md) counts assignments by joint suffix feasibility.

[Principal minors](marker-principal/README.md) characterize feasibility of a singleton guarded system with an odd marker. A [component solver](scc-guards/README.md) constructs model bases when all within-component arcs have their reverse. [Witness charts](chart-basis/README.md) compile acyclic guards with few terminal clauses and exhibit a limit on testing arbitrary proposed chart covers.

[Fourier interfaces](fourier-interface/README.md) count affine-factor models on a supplied binary tree in polynomial time times 2^(3w/2), where w is the maximum shared row-space dimension. [Paired principal minors](paired-minors/README.md) show a coNP-completeness barrier for a broader comparison problem associated with the directed marker criterion.

[A clause-violation Gram test](violation-certificates/affine.md) recognizes exact bounded-degree certificates and recovers a model count. [Conditioning and component products](violation-certificates/hybrid.md) enlarge this tractable class. [A width-three grid](violation-certificates/width3.md) separates the tests, while [balanced-cut barriers](violation-certificates/barrier.md) bound the reach of the specified coordinates.

[Fixed-width counting consequences](fixed-width-counting/README.md) derive exact counts under affine and quadratic constraints and a size tradeoff for circuits with fixed-width CNF gates from the October manuscript.

[Hidden cut recovery](violation-certificates/hidden.md) recognizes an equivalent interaction under the stated bounded-width and bounded-degree promise. Polynomial recursive counting requires the same promise on connected restrictions.

[Exhaustive residual gate search](residual-gate-bound/README.md) excludes every normalized L-meta-18968 residual circuit with at most 23 gates. The raw decoder and native verifier are included.
