# A fixed 29-gate prefix admits no eleven-gate crown completion

The twelve-crown predicate is true on input pair $(i,j)$ exactly when $i\ne j$. The first twelve raw wires indicate the row and the next twelve indicate the column. Each block has exactly one true wire. The 29 binary gates in `prefix.txt` leave 53 wires available. Operation 0 is OR and operation 1 is AND. Gate indices and wire indices start at zero. Gate $k$ writes wire $24+k$.

**Claim.** No suffix of at most eleven binary AND/OR gates, with arbitrary fanout, appended to this particular prefix computes the twelve-crown. This fixed-prefix exclusion allows every AND count.

Run `python3 verify.py` in this directory with Python 3.10 or later and a C++17 compiler named `c++`. The verifier regenerates the entire census from the 29 gates and checks every branch. It uses only the Python and C++ standard libraries.

## Distinct source wires

Prune gates that cannot reach the output. A live suffix with $g$ gates uses $2g$ input pins and at least $g-1$ pins refer to earlier suffix gates. Thus at most $g+1\le12$ distinct raw or prefix wires can feed the suffix. An output taken directly from an existing wire uses one source.

For every off-diagonal input $p$ and diagonal input $n$, some selected source must be true at $p$ and false at $n$. Otherwise monotonicity forces the output on $p$ to be at most the output on $n$. The 1,584 pairs yield 50 inclusion-minimal sets of distinguishing wires. A possible source set must meet each of the 50. The verifier branches on an unhit set and tries each of its wires. Pairwise-disjoint unhit sets give a lower bound on how many further wires are needed. Once all sets are hit, the verifier includes every extension up to size twelve. The resulting counts are 2 sets of size ten, 109 sets of size eleven and 2,868 sets of size twelve. No smaller size survives.

## Twelve distinct sources

All twelve source wires and all ten non-output suffix gates must each feed exactly one pin, so the suffix is a read-once formula. For a positive and a negative input, trace a path to a distinguishing leaf. At an OR let the positive input choose a true child and at an AND let the negative input choose a false child, fixing deterministic choices for ties. The pairs reaching any leaf form a rectangle because every choice restricts just one player's input. Each source occurs in only one leaf.

For a chosen support, project the test inputs onto that support. Use the minimal positive projections and maximal negative projections as test cases. In their matrix of pairs, a single available distinguishing source forces the pair into that source's rectangle. The product of its forced rows and forced columns must belong to the same rectangle. Iterating these implications yields a contradiction for all 2,868 supports.

## Ten and eleven distinct sources

Represent each outstanding use of a wire by a token bearing its 144-bit truth table. Start with one token for each distinct selected source. Processing a gate consumes two tokens and emits one token for its result. A source or intermediate result used more than once receives one extra token per additional use. A live $g$-gate suffix ending with one token and starting from $m$ distinct sources therefore uses exactly $g+1-m$ extras. The upper bound of eleven gates gives a budget of $12-m$ extras.

The C++ checker tries all allocations to sources and every subsequent unordered pair of tokens, both operations, and all affordable copy counts for each result. Induction on a circuit's topological order shows that its execution occurs among these choices. Equal truth tables are interchangeable on the 144 tests. A remaining token must still distinguish each positive-negative pair. When merging a pair, the only obligations that can be lost are those distinguished by one token in the pair alone or by exactly the two tokens in the pair. The checker tests those obligations on the new token and rejects a failing merge. The final token must equal the full target truth table.

Every recursion consumes one unit of the sum of the current token count and remaining copy budget. Memorizing unsuccessful token multisets preserves the search result. All 111 smaller source sets are exhausted without a compatible output.
