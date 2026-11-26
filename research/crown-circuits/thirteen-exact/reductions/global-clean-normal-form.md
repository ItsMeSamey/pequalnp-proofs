# A terminal comparison normal form for the 12-crown

Consider monotone fan-in-two circuits on the 24 raw row and column indicators, required to return 0 on twelve equal-label inputs and 1 on every unequal-label input. Any minimum-size circuit has an equivalent circuit of the same size with this structure:

* Every signal in the prefix is true on at least one equal-label input.
* Each of k subsequent AND gates reads two prefix signals whose sets of true equal-label inputs are nonempty and disjoint. Their outputs cover all 132 positive cells.
* The final k − 1 gates form an OR tree over the k AND outputs, for some k ≥ 1.

Raw signals count as prefix signals. No assumption is made about the depth, gate types or sharing of the original circuit. In the resulting prefix, each AND has parents whose diagonal truth sets overlap and are incomparable under inclusion. Thus each parent of a prefix AND is true on at least two diagonals, and their union has at least three labels. Every use of a raw input by an AND lies in the terminal comparisons. In particular, any AND with fanout at least two lies in the prefix.

## Proof

A wire is called clean if it is false on all twelve equal-label inputs. The output is clean, and every raw input is true on exactly one diagonal. The function is nonconstant. We may remove unused gates, propagate constants, and bypass unary or repeated-input gates without increasing the gate count. An invalid forward read is a constant false. Thus a minimum circuit can be taken to have two distinct valid inputs at each gate. These simplifications do not use a promise beyond preserving the outputs.

A monotone gate admits the following bypass on the promised matrix. If an earlier wire is at least as true as the gate on all positive inputs, and at most as true on all negative inputs, replacing the gate by the wire preserves the target. Applying monotonicity to the suffix on each input proves this at every fanout. The bypass removes one gate. In a minimum circuit an AND therefore cannot have comparable diagonal truth sets at its parents: bypassing to the smaller parent preserves all diagonal values and can only increase positive values. Dually, an OR's parent truth sets on the positive inputs must be incomparable. In particular an AND never takes a clean parent.

Call an OR mixed if its output is not clean and exactly one parent is clean. Every nonclean gate consuming a clean signal is such an OR. For each mixed OR bypass it to its nonclean parent. Keep the value of each distinct formerly consumed clean wire as a candidate output disjunct. Perform the rewrites in topological order, interpreting every wire reference after previous bypasses. All values on equal-label inputs stay identical, by induction in the gate order. Consequently clean wires stay clean, nonclean wires stay nonclean, and deleting one mixed OR creates no other mixed OR among surviving gates.

Append an OR of the redirected former output and all distinct collected disjuncts. This costs at most one OR per deleted mixed OR. On an equal-label input all the added disjuncts and the old redirected output are false. On an unequal-label input where the redirected output is false, take the first wire whose old and transformed values differ. Such a wire exists because the original output was true. It is a bypassed mixed OR: changing an ordinary gate value requires an earlier change. Its original clean input was true and still has the same value by its earlier position. This input is a collected disjunct, hence the new output is true. The transformation therefore preserves the represented graph and never increases size.

All clean nodes of the transformed circuit now form the final region. An OR in that region takes two clean signals, since a true diagonal at either parent reaches the OR. Every clean AND has two nonclean parents by minimality. Each such AND requires disjoint, nonempty diagonal truth sets at its parents. Remove unused gates. Expand the output logically as an OR of the distinct reachable clean AND outputs, and denote their number by k. The output is nonconstant and no raw wire is clean, so k ≥ 1. A connected binary OR network joining k source signals to one output uses at least k − 1 gates: if it has q gates then it has k+q vertices and at most 2q incoming edges, hence k+q−1 ≤ 2q. Replacing that network with an OR tree of k−1 gates preserves the gate budget. The remaining nonclean gates depend only on nonclean signals and can be topologically ordered ahead of the k comparisons.

The entire construction starts with a minimum circuit, so each equivalent representation with no larger size remains minimum. Applying the AND-parent incomparability to the resulting prefix establishes the final claims.

## Numerical consequence

For a normalized minimum circuit of size s, the prefix contains exactly s−2k+1 gates. Starting from any candidate of at most 40 gates therefore gives a normalized representation with at most 41−2k prefix gates. The prefix may contain shared ANDs with overlapping diagonal supports. The terminal comparison inputs are unrestricted prefix wires, and no rectangular form for their positive-cell truth sets is assumed.

## Fanout in every minimum circuit

Even before normalization, any clean wire has fanout at most one. Every consumer is an OR. If there are t distinct consumers, bypass all of them to their other parents and append one OR of the new output and the original clean wire. When the wire is false every bypass is exact. When it is true the input is positive and the appended disjunct accepts. The wire itself occurs earlier than all its consumers. Thus t ≥ 2 would remove at least one gate in total. Dually, every wire true on all off-diagonal tests has only AND consumers and fanout at most one: bypass the consumers to their other inputs and append one final AND with that wire. A genuinely shared signal therefore fires on some equal-label input and misses some unequal-label input.
