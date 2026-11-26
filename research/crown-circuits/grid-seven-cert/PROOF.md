# The seven aggregate signals require exactly twelve suffix gates

Label the twelve grid cells by three rows and four columns. The 29-gate OR prefix first forms the union of the two raw input wires for each cell. It then forms the union for each of the three rows and four columns. The seven resulting signals indicate which rows and columns contain at least one of the two selected cells.

**Claim.** A monotone binary AND/OR circuit with only these seven signals available as sources needs exactly twelve gates to distinguish different cells from identical cells. Arbitrary DAG sharing is allowed.

The upper bound takes four gates to detect at least two active rows, seven to detect at least two active columns, and one to OR the results. The verifier constructs the 12-gate suffix and checks all 144 ordered pairs of cells. For each of the seven aggregate signals the verifier also finds a positive input and a negative input for which this signal is the only one true on the former and false on the latter. By monotonicity, all seven sources must occur.

For the lower bound, prune unused gates. Represent every use of a source or intermediate signal with a token carrying its Boolean function on the 144 inputs. Each live binary gate consumes two tokens and generates one result token plus enough copies for additional uses. With seven distinct sources, a live circuit of at most eleven gates needs at most five extra copies in total. The search considers copies of original sources and copies of intermediate results.

At each step the checker tries every unordered pair of tokens and both operations. If an off-diagonal input is true and a diagonal input false at the desired output, some remaining token must be true on the former and false on the latter. The checker rejects merges violating that necessary condition, then recurses with every affordable copy count. Equal token multisets with equal remaining budgets have identical possible continuations. A final single token is accepted precisely when it agrees with the full target. Processing any proposed circuit in topological order gives one of the enumerated executions, so exhaustion establishes the lower bound.

Run `python3 verify.py` with Python 3.10 or later and a C++17 compiler named `c++`. The source set is restricted to the seven specified aggregates. Other raw wires and other prefix outputs are outside this theorem.
