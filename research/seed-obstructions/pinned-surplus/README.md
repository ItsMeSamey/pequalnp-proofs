# Gate surplus under constant restriction

The source is GateSurplus.lean. It imports the physical indexed circuit and Monotone2 from the pinned PEqualNP project, and uses its Circuit.eval and gate-size convention. Each formal input is a distinct physical wire. The supported original cone has binary AND/OR gates with both operands earlier than the gate; repeated operand indices are allowed. Only gates and distinct source wires reachable from the designated output count. The assignment domain can be an arbitrary family of samples.

The forward pass annotates each wire as fixed zero, fixed one, or open. At a gate with a neutral input it retains the opposite operand. Other gates keep both operands. On every assignment respecting the pins, the annotated physical circuit with explicit unary copies has exactly the original output. If the root cofactor is nonconstant it must be open, and every parent demanded by an open gate's simplification is open.

A backward scan starts with one demand for the output. On the original side a demanded gate replaces its own name by both of its operand names. On the restricted side only the retained names enter the demand set; a one-parent bypass costs zero binary gates. When a name occurs on both sides of the scan, inserting a parent into the larger demand set can increase its size no more than inserting it into the subset. This is the local reason that the sum of kept gate count and full frontier size never exceeds the sum of full gate count and kept frontier size. Identifying previously distinct input variables is outside this calculation.

The physical compiler realizes the final demand set using raw source wires, then walks back up the scan. At a one-parent bypass it copies a wire index. A two-parent gate appends one actual AND or OR to a physical gate list. Unreachable gates append nothing. If at most t distinct formal input wires are open, pinned_minor_bound returns a circuit D that agrees on every allowed assignment and satisfies
`D.size + old number of occurring sources ≤ old reachable gate count + t`.
For connected nonconstant output cones this is the usual gate budget `t − 1 + old surplus`, where surplus is gate count minus distinct input count plus one.

The file concerns pinning of formal boundary inputs. An identification of two surviving input wires needs its own accounting.

To replay, run `./check.sh` with the dependencies built in the pinned upstream checkout at commit `b104ff3988c176aae2db960c2a71ddf975ef047c` using Lean 4.36.0. The script defaults to the shared project checkout. Set `LEAN_PROJECT` to another upstream lean directory if needed.

The theorem `reindexed_pinned_minor` also accepts a smaller physical input list, an explicit wire renumbering, and a proof that corresponding surviving wires agree on the samples. It produces the compact circuit directly on that smaller input list. Its source budget still counts the original unpinned names, even if the renumbering identifies two of them.

In `reindexed_pinned_minor`, evaluations agree on the supplied rows. The old counts are the gates and input names reachable from the designated output. The bound charges each distinct surviving original name in `free.card` before renaming, including names with identical columns on those rows. Renaming may identify coincident columns without reducing this charge. A computed signal must be explicitly supplied as a column to serve as a free source. Injectively renaming physical wires gives the pin-and-prune specialization.
