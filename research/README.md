# P versus NP research checkpoints

The files on this branch contain partial results in both directions. The full P versus NP problem and both assigned circuit steps remain open in this work.

| Direction | Checked result | Outstanding question |
| --- | --- | --- |
| SAT algorithms | A matching between clauses and distinct variables certifies satisfiability. Given a core of variables and a matching covering every other clause outside that core, Lean proves that solving the internal clauses suffices. | The matching-based algorithm can require exponentially many assignments. See the [solver, tests, and counterexamples](hall-solver/README.md). |
| Incidence circuits, L-meta-2794 | For a projective plane with N points and N lines satisfying the posted assumptions, every allowed circuit passing the tests has at least 2N gates. This gives the requested bound for orders 101 through 200. On every sparse right input the circuit must compute incidence exactly. | The target asks for at least Nq/100 gates for every order q greater than 100. The verified linear bound leaves larger orders open. |
| Finite circuit synthesis, L-meta-8032 | Lean checks that the 24 listed masks are exactly the maximal independent masks. Passing the 16 positive and 24 negative tests therefore determines any monotone output on all 2,048 inputs. | The step asks to rule out a circuit with at most 21 gates and at least three specified dirty AND gates. The truth-table equivalence does not bound the number of gates. |
| General circuit counting | When the number of circuit descriptions is smaller than the number of Boolean truth tables, every evaluator misses a truth table. | Counting does not put a hard language in NP. |

From a checkout with the pinned Lean and Mathlib dependencies installed, run `research/check.sh` to check the formal statements and the executable SAT tests. To reuse a separate checkout with the same pinned dependencies, set `PNP_LAKE_DIR` to its `lean/` directory.

The bounded-occurrence SAT case formalizes a classical result. See [Tovey, *A simplified NP-complete satisfiability problem* (1984)](https://doi.org/10.1016/0166-218X(84)90081-7). The [gate elimination notes](incidence-deletion.md) record a possible improvement to the incidence lower bound. The packing lemma is machine checked. The repeated circuit rewiring argument in those notes still requires formal verification.

The [21-gate candidate](../lean/Research/EdgeCandidate.lean) passes 39 of the 40 tests and has three dirty AND gates. It misses the positive edge (1, 4).
