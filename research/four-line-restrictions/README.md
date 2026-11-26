# Four lines with the supplied point ORs require 19 gates

For each of the 35 choices of four of the seven suffix lines, keep the positives on the chosen lines and project away the other line bits. Retain every original point input, including the 18 supplied point ORs. The minimum monotone fan-in-two gate count is exactly 19 on all 35 restrictions. Consequently the seven-line residual requires at least 25 gates. Exact transfer to L-meta-18968 gives at least **26 gates for the raw suffix**, with unrestricted wiring and output topology.

## Upper bound and point deletion

Four ordinary stars compute the four disjunctions of four incident points, gate each with its line and combine the four terms. This uses 19 gates. For the lower bound, let p be a retained positive on raw point q other than point 1. The checker finds an actual negative n with p outside n only in the single raw point coordinate q, even with all 18 free point ORs in the comparison. That witness persists after other lines are zeroed, since p uses only its own line. Thus every separator uses q. Set the standalone raw point coordinate q to zero, leaving the supplied OR coordinates formally untouched. Positives on the other points already have q false, and negative outputs can only decrease. Simplifying the first gate fed by q removes at least one gate. An unaffected positive rules out q itself as the output.

Repeat for every discarded point incident on some retained positive, except point 1. Previous substitutions preserve the private witnesses of the remaining points. After these paid deletions, lower every supplied point OR by intersecting its support with the retained core points. Set other point coordinates to zero. This preserves all core positives and preserves rejection at negatives. Zero and duplicate columns can be simplified for free. The checker usually retains the points incident to at least two selected lines and also retains point 1 if incident. For a small concurrent core it adds one private point per line. The generated cores and deletion counts are recorded by the program. Every core rejects the budget 18 minus its paid deletions.

## Line deletion

For any retained set S of at least two lines there is a line L whose deletion saves two gates. For each L and each raw point q, the checker finds a positive-negative pair with L as its unique separating coordinate and q active in the negative. Such a pair also exists with q replaced by any other line. Its positive uses only L, so the witness survives zeroing lines outside S whenever the named negative coordinate remains relevant.

Take the earliest gate reading a line L in a minimum circuit. Its other operand is a point-only wire or another line. If L has at least two distinct uses, setting L to zero removes both uses by constant simplification. If L has just one use, that use cannot be OR with another line M, since a private pair for L with M active in the negative would then be ordered on all remaining signals. For a point-only OR partner, its value must be true on some singleton q occurring in a retained positive. Otherwise replacing the partner by zero and simplifying the gate preserves separation with fewer gates. The private negative for L that contains q also activates the partner by monotonicity. Again the OR loses that private pair. The sole use must therefore be AND. This gate has an output consumer, since it is false on positives on every other retained line. Zeroing L removes the AND and at least one consumer. Idempotent equal-input gates and dead gates can always be dropped. All remaining required positives have L false and negative outputs can only decrease.

Applying the deletion three times gives the four-line lower bound plus six gates. The raw suffix adds one more gate by the exact front transfer.

## Exhaustion and replay

With GCC, an AVX2-capable x86-64 machine and Python 3.10+, run the following from this folder. The second Python argument identifies the research folder holding the pinned L-meta-18968.json and its verify_packing.py decoder.

```sh
g++ -std=c++20 -O3 -march=native verify.cpp -o /tmp/l-meta-four-paid
python3 run.py /tmp/l-meta-four-paid ../seed-obstructions
```

The core verifier adapts research/residual-gate-bound/verify.cpp to the generated dimensions. It enumerates every support of at most g+1 primitive wires that hits all positive-negative differences. It searches arbitrary AND/OR gates, permitting each input to be retired or kept. Starting with d inputs, a connected cone of at most g gates has at most g+1-d extra operand uses, so a transition retaining k of its operands consumes k units. Every state must still distinguish every positive from every negative. On a positive-negative pair distinguished only by i, retiring i in an AND with j requires j on the positive, and retiring i in an OR requires j absent from the negative.

A gate whose output is zero on all positives or one on all negatives simplifies to a constant preserving separation. A gate dominated by an existing live wire (at least as often true on positives and at most as often true on negatives) can be replaced by that wire. Equal operands can be removed, and duplicate recipes can be shared. Among the remaining gates choose the lexicographically smallest currently available unordered recipe tuple (larger source, smaller source, operation). Each newly enabled recipe references the newest wire, so the tuples increase. These reductions preserve a minimum witness. A single surviving wire is conservatively accepted. All 35 searches terminate with no accepting state.
