# An eight-input minor retaining six ANDs needs at least fourteen ORs in any proper extension

Let a fan-in-two monotone circuit on n>8 inputs compute threshold two using six ANDs. Restrict any n−8 inputs to zero. Suppose the resulting circuit still uses all six original ANDs and is simplified by folding zero operands at ORs and deleting unused ORs. Then the simplified circuit has at least fourteen OR gates.

A fold replaces a zero branch by the surviving branch. Any original OR-only path from a retained raw to an operand of a retained AND survives these changes, since no such path enters a wire that is identically zero. Conversely every surviving OR-only path expands into an original one. Removing unused ORs cannot affect the operands of the retained ANDs. Thus all eight original signed raw masks, on the six original comparison axes, agree with the masks in the minor.

If there were at most thirteen ORs the known eight-input size minimum of nineteen forces precisely thirteen. The one-through-five singleton-hot exclusions then make all six ANDs singleton-clean, since a threshold circuit necessarily has at least one singleton-clean output-exposed AND. The all-clean cover criterion in ../uniform/single-level-extremal-cover.md applies at n=8, a=6, and OR excess one: those eight original formal masks cover the full six-axis sign cube. The theorem in signed-cover-extension.md forbids even one additional raw, contradicting n>8.

This proof does not require raw regularity, a pure group, a minimum-size original circuit, or a condition on its OR count. The hypotheses concern preserving the six axes and the OR-only paths in the chosen restriction.
