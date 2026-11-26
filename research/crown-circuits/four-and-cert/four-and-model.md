# Four-AND normalized crown circuits

Consider a monotone fan-in-two circuit computing inequality on the 12×12 one-hot promise. Choose a minimum-size circuit among those using at most four ANDs. The terminal-clean normalization applies with this restriction: bypassing removes gates, moving a clean disjunct to the output replaces an OR by at most one OR, and rewriting its final OR network uses only OR gates. None of these operations increases the AND count. In particular, an AND with a clean input is bypassed to that input, which preserves diagonal zeros and can only grow positive values. Let k be its AND count and let p be the number of terminal clean ANDs. The output is the OR of the p terminals; the other d=k−p ANDs occur earlier and each is true somewhere on the diagonal. Remove unused gates and simplify constants and identical inputs. All 24 raw wires are essential as sources in this circuit: for a row i, if the raw row i were absent, then (i,j) after removing the row signal would be just column j. Positive (i,j) and monotonicity would imply true at diagonal (j,j). The column argument is symmetric.

Expand the OR-only portion separately down to each AND pin, stopping when an AND is encountered. Each pin is the union of its formal raw input (the OR of all raw sources reaching it through OR-only paths) and a subset of earlier dirty gates. This defines a monotone Boolean function F on 2k formal raw bits, along with d masks specifying all pins reached directly from each dirty AND. Enumerate every such skeleton, removing interchangeably ordered pins. For each of the 2^k global choices of one parent per AND, recursively collect the formal pin bits reached from any terminal. These are the clauses of a monotone CNF for F: choosing one parent makes an upper bound for F, and for any assignment making F false one can choose false parents simultaneously at all false ANDs. Remove clauses containing another.

For each physical label i choose a clause C_i falsified by its two raw incidence masks, meaning both are disjoint from C_i. Two labels cannot choose the same clause, since the corresponding offdiagonal must be true. Consequently each raw mask at label j hits every chosen C_i with i different from j. On every unchosen clause, an offdiagonal (i,j) must have at least one of the row or column mask hit the clause. Each dirty AND must evaluate true at the complement of some minimal clause by monotonicity and its nonempty diagonal.

Remove all ANDs and the final OR tree and regard the remaining OR-only network as a multiple-output union circuit with 24+d named sources and 2k named output pins. Distinct output pins may point to the same node. Every source is used, including every dirty output, by liveness and raw essentiality. If it has q OR gates, reverse its incidence DAG: each pin is now a fresh singleton mask, and a node takes the union of its outgoing-use masks (including separate named-output uses). A node of outdegree t costs t−1 binary unions. The total is 2q+2k−(q+24+d)=q+2k−24−d. Thus an original network of size g, where q=g−k−(p−1), gives a reverse union library costing at most g−23. Simplification can only lower the cost. A library must contain the 24 chosen physical masks and all prescribed dirty-output incidence masks.

To test g≤40, select at most 17 nonsingleton library masks. For every selected nonsingleton mask require a pair of selected proper subsets whose union is that mask. This is sufficient for an acyclic library because both operands have fewer set bits. Include singleton formal inputs for free. For each label/shore choose an available mask consistent with its assigned clause and the other labels' assigned clauses. For every unassigned clause and every offdiagonal pair enforce coverage by one of the chosen shore masks. The resulting finite CNF is necessary. The independent unrestricted reconstruction available in reconstruct.py evaluates a candidate on all 144 cells.

For two terminals there is at most one unassigned clause. It suffices to use the same available mask for both shores of each label: if at most one row misses the extra clause, duplicate all row masks; otherwise all columns hit it, and one can duplicate all column masks. This preserves the same library budget and all other clauses.

## Reproduction

Use Python with python-sat (including the CaDiCaL 1.9.5 binding) and drat-trim. Set the DRAT_TRIM environment variable to the checker executable if it is outside PATH. Run these commands from the certificate directory.

```sh
python verify.py 1 17 >audit1.log
python verify.py 2 17 >audit2.log
python verify.py 3 17 >audit3.log
python verify.py 4 17 >audit4.log
python check_counts.py
python reconstruct.py verified-41.json
```

Each invocation exhausts all surviving skeletons and diagonal-clause assignments up to renumbering AND gates within their dirty/terminal classes, reversing individual AND pins and reordering physical labels. The executable loops through every input assignment before quotienting. Every retained negative case generates a DRAT proof and independently checks it against the generated DIMACS file. Fewer than four AND gates can supply at most eight clauses, so twelve distinct diagonal clauses are impossible. The one-terminal, four-AND case has no eligible skeleton.
