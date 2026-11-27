# Physical bilateral OR-spine normalization at order 401

The input is the scalar two-shore monotone circuit with literal operand positions. There are 161203 sites per shore, 402 points per line, and a unique line through each pair of distinct points. The output accepts incident singleton flags and rejects independent masks of arbitrary points and at most 401 lines.

Binary preprocessing forwards copy and zero gates. Ancestor compaction retains original input labels and the entire output predicate, with size bounded by the original. Physical liveness means every gate is an ancestor of the selected output.

For a chosen shore the algorithm traces each raw owner's unique outgoing operand through successive ORs. A selected OR has a principal port and a sibling. On a protected private path the physical input and gate equations show that a true sibling masks any effect of changing the owner. An independent sparse test with a true sibling would then contradict sensitivity on an incident flag. The plane supplies a fresh neighbor because at most 401 excluded owners block its 402 choices. The line stage retains the original sparse domain. The point stage covers 401 points and 400 lines. Independent singletons exclude conflicting orientations of a gate.

The allocator forwards each selected principal reference, emits the kept gates, and appends one OR per saved sibling. Its total size equals the binary source size. Its output equals the transformed old output union the transformed siblings. The appended chain makes each sibling live, and every old output ancestor maps to a new output ancestor. Both stage results retain physical liveness.

Opposite-shore literal multiplicities include both uses of a repeated operand. The final raw reference of a selected owner equals the reference of its walk endpoint. A zero-use endpoint would shield the output from a change on an incident flag. If the transformed raw has one use, weighted transport forces its original exit to have one use and to feed an AND. That surviving AND port accounts for the new unique reader. The point transform preserves line multiplicities and the once-read AND property established by the line transform.

The two census experiments and the final deletion iteration use the resulting live physical circuits. Their numerical inequalities remain separate obligations.
