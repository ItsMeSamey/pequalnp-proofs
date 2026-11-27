# Balanced read-twice width-three CNFs at point 2 over F₃

For every Boolean CNF Φ there is a polynomial-time constructible signed CNF Q of width at most three such that its canonical multilinear extension satisfies

$$\widetilde Q(2,\ldots,2)=\#\mathrm{SAT}(\Phi)\pmod 3.$$

Every raw variable of Q occurs exactly once positively and once negatively, in two distinct clauses. There are no repeated literals, tautological clauses, or duplicate clauses in Q. The equality preserves the full residue, including zero. In particular the decision test for a nonzero value is Mod₃P-hard. The same construction for a deterministic witness verifier gives its generating polynomial by projecting one raw success parameter to each input indeterminate and all remaining parameters to 2. In particular it gives a direct F₃ projection to the directed Hamiltonian cycle polynomial.

## From assignments to a weighted graph

For each source variable, create two literal vertices of activity 1, join them by an edge, and give them one common neighbor of activity −1. For fixed literal states the edge excludes simultaneous occupation, while summing the common neighbor cancels the both-empty state. Each source clause gets an activity −1 vertex adjacent to its distinct literal vertices. The sum over this vertex is 1 if at least one literal is occupied and 0 otherwise. Thus the independent-set sum of this graph H is the number of satisfying assignments in F₃. An empty source clause gives an isolated activity −1 vertex and cancels the whole sum. Unused variables can be kept as literal pairs, so their assignments are counted as well.

For a polynomial verifier, use Boolean gate equivalences and pin the output to true. Each accepted input then has one extension to the auxiliary Boolean variables. For each weighted input e one may add a selector adjacent to its negative literal, with activity −(1−Xₑ). If e is false the selector must be empty. If e is true its conditional sum is Xₑ. Taking the verifier for directed Hamiltonian cycles from [the positive-CNF construction](read-twice-positive-cnf-projection.md) yields HC with each arc indeterminate projected into just one raw parameter. Selectors are absent in the all-2 counting reduction.

## Edge and equality identities

Write R for the matrix with rows (1,1),(1,0) and Dₐ for diag(1,a). Replace each original vertex of degree d by d incidence copies between two free terminals in a path, attaching each original edge to its incidence copy. The path has d+1 links, also when d=0. Implement each link by six R edges with five intervening activities −1,−1,1,−1,−1. Ordinary multiplication gives

$$R D_{-1} R D_{-1} R=\operatorname{diag}(-1,1).$$

Joining two copies with D₁ between them gives the identity matrix. Conditional on the shared state, activities of the copies and terminals multiply. Each incidence copy has degree three, each terminal degree one, and every equality internal degree two.

Make one clause per expanded vertex. For each expanded edge create one raw variable, give it success parameter 2, and insert it positively at one endpoint and negatively at the other. Expand the product of clause indicators by choosing failed clauses with inclusion-exclusion sign −1 per chosen clause. When neither endpoint is chosen the edge contributes 1. Choosing just one forces either raw value 0 or raw value 1, each of weight 2 in F₃. Choosing both forces contradictory values. Therefore its interaction is

$$\begin{pmatrix}1&2\\2&0\end{pmatrix}=D_2 R D_2.$$

There is no extracted edge scalar. A degree-a vertex receives effective occupied activity −2ᵃ. In particular degree one and degree three give +1, and degree two gives −1. A positive private input at a clause multiplies this activity by its failure parameter. Use a private input at 2 on the middle of each equality gadget, changing its activity to +1. Use one on a terminal of every ordinary activity −1 source vertex. For a selector use one at 2 on the first terminal and one projected directly to Xₑ on the second terminal. Their combined contribution is −(1−Xₑ) when occupied. All private inputs occur initially at vertices of degree at most two.

## Balancing every private input

For each positive private input p create four fresh raw inputs g₀,…,g₃ at 2 and four clauses (¬gᵢ₋₁ ∨ gᵢ), with indices cyclic modulo four. Append ¬p only to clause 0. If p=1, all four implications apply and the gadget has two satisfying assignments. If p=0, only the other three implications constrain g, giving the five nondecreasing four-bit words. At point 2 every assignment to the fresh g variables has weight 2⁴=1. Both conditional sums are therefore 2 in F₃, also when p has a formal success parameter. All private gadgets together multiply the result by 2ᴾ, where P is the number of private inputs. If P is odd, append a fresh four-cycle of implications without a private input. Its value is 2, so the total scalar is 1.

The original occurrence of p and its new occurrence have opposite signs and lie in separate clauses. Every fresh g has one occurrence of each sign, in separate clauses. The physical edge variables already have this property. Distinct expanded clauses have distinct signed literals, and each cycle uses fresh variables. The construction uses no repeated unit clause.

## Exact size

Let v and e be the vertex and edge counts of H, let n₋ count ordinary activity −1 vertices, and let s count formal selectors. Put L=2e+v, the number of equality links, P=L+n₋+2s, and δ=P mod 2. Before balancing, the expanded graph has 2e+2v endpoint/copy vertices and 5L internal vertices, together with e+6L edges. The final physical CNF therefore has

* **Raw variables:** 13e+6v+5P+4δ.
* **Clauses:** 12e+7v+4P+4δ.
* **Literal occurrences:** exactly twice the raw-variable count.

The degree-three incidence clauses have no private input. The degree-two equality clauses have at most one, and the degree-one terminals have at most one. Each padding clause has width two or three. This proves the width-three bound for unbounded-width source clauses as well. For the all-2 case, independently, any CNF Q with m raw variables satisfies $\widetilde Q(2,\dots,2)=2^m\#\mathrm{SAT}(Q)$ in F₃. The reduction above normalizes the residue of the *multilinear evaluation* exactly.

For point-2 decision membership, a nondeterministic machine guesses the assignment and makes two accepting branches for every satisfying assignment when m is odd, one when m is even. It has a nonzero number of accepting branches modulo 3 exactly on the nonzero-evaluation instances. Together with the direct reduction from nonzero-#SAT modulo 3, this gives Mod₃P-completeness. Under the usual modular counting function convention the construction preserves the output residue directly.
