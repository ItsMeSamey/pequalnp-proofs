# A 25-gate lower bound for the normalized L-meta-18968 residual

Every fan-in-two AND/OR circuit separating the 28 required positive rows from the 245 maximal negative rows on the 38 normalized primitive signals uses at least **25 gates**. Fan-out is unrestricted. This is the residual with the front supplied separately. The bound alone leaves the 33-gate residual feasibility question open.

## Replay

From this directory run the following with Python 3 and GCC on an AVX2-capable x86-64 machine.

```sh
python3 decode.py > /tmp/l-meta-residual.rows
g++ -std=c++20 -O3 -march=native verify.cpp -o /tmp/l-meta-residual-verify
/tmp/l-meta-residual-verify 24 < /tmp/l-meta-residual.rows
```

The decoder imports the adjacent seed-obstructions verifier, which checks the formal-statement hash and decodes the 676 raw columns. It projects onto the 38 primitives, checks that omitted signals vanish on all required positives, and retains maximal negatives. It also checks that front-covered rows are dominated after projection. The search exits successfully with these support sizes and counts.

```text
20 1
21 18
22 154
23 831
24 3165
25 9023
```

## Completeness

For every positive row p and negative row n a separator uses some bit of p outside n. The decoder verifies that the inclusion-minimal differences are singletons on bits 0 through 19 except bit 1, together with the pairs {1,20}, {1,21}, {1,31}. The verifier enumerates every support satisfying these requirements with at most 25 inputs. A connected binary circuit with g gates has at most g+1 inputs.

Choose a minimum circuit, remove unused gates, and order its gates topologically. A state retains each signal until its last use. For every new AND or OR gate the search chooses its two distinct operands and which operands retire at this gate. An equal-input gate can be removed by idempotence. If a gate retires d inputs, then the remaining gate budget decreases by one and the number of live wires changes by 1−d. The excess of remaining budget over the minimum needed to connect the live wires therefore falls by 2−d. The initial excess is 24 minus the support size plus one. A negative excess cannot yield a connected circuit.

If a negative dominates a positive on live wires, no monotone continuation separates them. For every positive-negative difference consisting of a singleton i, retiring i in AND(i,j) requires j true on the positive, and retiring i in OR(i,j) requires j false on the negative. The verifier obtains these witnesses by intersecting the negative columns for all the positive's live set bits except i. The complete intersection is empty before the singleton test. Reaching a single live wire is conservatively counted as a possible solution.

Two further reductions preserve a minimum circuit. Number gate outputs consecutively from 38. Repeatedly choose the available gate with least tuple (larger source, smaller source, operation). Each newly enabled gate uses the newest, largest source, so this ordering has strictly increasing tuples after identical gates are merged. The verifier enumerates this ordering. Finally, if an existing live wire is at least the proposed output on positives and at most that output on negatives, substituting that wire at every use of the new gate preserves separation by monotonicity and saves a gate. The same argument applies to a gate constantly zero on positives or constantly one on negatives, using the corresponding constant and simplifying. Both labels occur, so simplification yields a constant-free circuit. Neither case can occur in a minimum circuit.

[Two extra point signatures](../two-extra/README.md) require at least 19 point gates when the other seven signatures are canonical, independently of mixed topology.

With zero or one spare use, [private positive and negative pairs](../seed-obstructions/suffix-search/COPY.md) further constrain an admissible tree or single-copy circuit. The native verifier uses the necessary recursive connectivity condition for zero spare uses and the necessary bipartiteness condition for one spare use. The [exact raw transfer](../seed-obstructions/raw-transfer.md) therefore gives at least 26 raw suffix gates.

[Four-line restrictions](../four-line-restrictions/README.md) independently give the same lower bound. Each of the 35 restrictions costs exactly 19 gates with every original free point OR retained.

The [point-deletion proof](../point-deletion-core/README.md) raises the residual lower bound to 28 gates and the unrestricted raw suffix lower bound to 29.

The [front-free branch](../front-free/README.md) needs at least 34 gates when wire 54 is omitted.

The [six-point core](../six-point-core/README.md) raises the unrestricted residual lower bound to 29 and the raw lower bound to 30.
