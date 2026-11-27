# Projected scalar tail for L-meta-20579, shard 53

**Provisional. Independent reviews by teams 07 and 11 are pending.** Run `python -BO check.py` in this directory using Python 3.10 or later. The replay uses only the standard library and checks SHA-256 digests before evaluating the certificates.

The frozen 32-by-32 relation uses one row and one column input on every cell. The control has 180 binary gates. We cut five product outputs, wires 220, 223, 224, 225 and 226. One scalar tail drives wire 220 and the four other taps read false. Replaying all 32 assignments at every cell gives 98 cells that require a nonzero tap, 613 that require zero, and 313 that allow either. The 26 paid donor bits distinguish 519 required input vectors. Wire 244 denotes the already paid NOT of old wire 121 and has six-diagonal marker 53. Wire 1000000 denotes false.

Six additional binary gates compute AND(153,244), OR(85,121), OR(23,68), OR(60,212), OR(50,81), and OR(31,49). The tail receives the unchanged donor wires 24, 63, 74, 86, 88, 99, 106, 109, 112, 131, 134, 136, 141, 154, and 208, followed by these six signals. Slot zero occupies the least significant bit. Projection yields 84 required-one and 385 required-zero patterns. Every slot is essential. The source path embedded in the historical projection JSON records provenance. Replay uses local files throughout.

The circuit model charges one unit per binary AND, binary OR and unary NOT. Fanout and input wires are free. Constants can be propagated and unused gates pruned. The projected tail is a single-output DAG whose only nonconstant inputs are the 21 positive wires just listed. The fixed merged context has 136 old gates plus its marker. Since every projected input is essential, the six additional gates are all live. The 170-gate target therefore permits a tail of at most 27 in this fixed decomposition.

## Proof order

1. `verify_projection.py` pins the control, checks its graph and gate codes against the local portable interface, and reconstructs the complete partial truth table.
2. `projected27.md` proves the first-branch orientation and grouping conditions. The certificates force at least 25 binary gates with any number of inversions. Binateness excludes a monotone tail. Thus three or more NOT gates require at least 28 gates in total.
3. `projected-two-not28.md` and `verify_projected_two_not28.py` exclude 25 binary gates with exactly two NOTs. They enumerate 66 partitions and test signed orientations and topological orders by checking necessary implications.
4. For one NOT, let M be the monotone operand of that inversion. Comparable care descents force values of M. The five-region trace relaxation and its refutation in `precone-region-result.txt` establish at least 25 binary gates producing M. On the increasing chain 1024, 17408, 17536, 17856 the output labels are 0, 1, 0, 1. The middle descent forces M to be 0, 0, 1, 1 by monotonicity. A final AND with the complemented M fails on the last point. A final OR with that signal fails on the first. The complemented M alone also fails. Hence at least two more binary gates lie strictly downstream of the NOT. The three disjoint charges total at least 28.

The conclusion applies to the fixed six-gate prefix and projected scalar bank, giving at least 171 gates in the specified decomposition. It does not exclude a different bank, a shared prefix redesigned with the tail, or a circuit with five separate replacement outputs.
