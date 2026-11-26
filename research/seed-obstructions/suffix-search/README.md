# Fixed-prefix exclusions for the 33-gate residual search

The target is the 676-column interface of R_meta_5882_317, with the last gate fixed to OR with front wire 54. The preceding 33 gates operate on the 38-signal residual interface. The two search seeds identify the recipe arrays in recipes.json. An operand indexes the 38 initial signals followed by earlier gates, starting at zero.

* For seed 18968, fixing its first 17 recipes leaves 16 gates. No completion exists.
* For seed 21968, fixing its first 16 recipes leaves 17 gates. No completion exists.

The remaining gates may be any binary AND or OR of available wires, with arbitrary fanout. The unrestricted synthesis problem remains open.

## Reproduction

Run `python3 verify.py` with Python 3.10 or later. The verifier decodes the formal statement in the parent directory. Its 676 residual rows and front and target columns were checked against theorem blob 31dd90b535fa7e4ef8bde6a7730ac77e49cc0c75. To check one instance, pass the numeric seed and prefix length as two arguments.

## Exhaustion argument

Each primitive or frozen gate output has a Boolean column on the 28 positive and 245 maximal negative rows. For each positive p and negative n the remaining circuit must use an available column that is 1 on p and 0 on n. Otherwise its input vector at p lies coordinatewise below its vector at n, contradicting monotonicity. The distinct starting signals used by the suffix must hit all these difference sets. A connected output cone with g binary gates uses at most g+1 starting signals. The verifier enumerates every hitting set within that bound, including supersets of minimal hitting sets. At each uncovered difference set it branches on the first available selected bit, excluding earlier candidates. Once all sets are hit, it enumerates all remaining choices within the bound.

For a support of d wires, the spare allowance is g+1-d. In topological order, apply each gate to two active wires. Remove each operand on its last use and retain it otherwise. Inserting the result decreases the active count by one minus the number of retained operands. A finished output cone has one active wire, so the total number of operand retentions equals the gate count minus (d-1). The verifier charges one spare unit per retained operand, including retained gate outputs. An equal-operand gate can be eliminated by substituting that operand downstream, and dead gates can be removed. Both operations preserve the output.

After each transition the active columns must still separate all positive-negative pairs. The state is completely described by its sorted multiset of columns, including multiplicity, and the spare allowance. The recursion considers every AND/OR transition and retention choice within the allowance and tests the final column directly. It rejects all 92 possible supports for the first instance (2 of size 16, 90 of size 17) and all 90 for the second (2 of size 17, 88 of size 18).
