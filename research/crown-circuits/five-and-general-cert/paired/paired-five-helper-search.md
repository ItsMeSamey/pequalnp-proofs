# Testing a 28-gate five-AND circuit for threshold two on twelve inputs

A paired size-40 crown yields a twelve-input threshold-two circuit with 28 gates. The known 41-gate crown has a 29-gate paired tail. Assume a size-minimum counterexample and then minimize its number of dirty ANDs (those true on some singleton). Terminal normalization places clean ANDs below a final OR tree.

In the transpose, there are 32 direction patterns. Each switch j has an active set U_j and produces U_j intersected with each of the two coordinate halves. Write B for the ten resulting branch masks, W for the distinct nonfull U_j outside B. The twelve raw receiver masks R_i have nonempty, pairwise disjoint complements. A circuit of 28 gates permits at most 17 reverse unions. The direct-receiver case is impossible by eleven-threshold-and-direct.md.

A dirty AND hot on singleton i has U_j contained in R_i: every resolution reaching it must see a true operand and hence must reach raw i. All raw masks are incomparable. Thus if U_j contains a receiver R_k, then R_k is contained in U_j contained in R_i and all are equal. Equality can be eliminated in a minimum-dirty counterexample: attach raw observer i to the existing activation of that split, rather than a later equal mask. All receiver truth sets on complete direction patterns are unchanged. The physical raw i is now downstream of that AND, so cannot make either input fire. The gate cannot fire on any other singleton by the containment just proved. All formerly full-switch terminals remain clean because no raw mask is full. If needed renormalize: in a size-minimum circuit the mixed-OR edits preserve the singleton values of surviving dirty gates, since the moved clean term is zero on each singleton. This contradicts minimal dirty count.

Consequently all useful nonreceiver unions can be built from branches and other nonreceiver unions. A raw receiver cannot be an OR ancestor of another terminal or of a distinct nonfull activation; bypass repeated masks. At most five distinct nonreceiver paid masks (helpers) are allowed, and they include every W. Every raw is a union of two available branches or helpers.

## Selector profiles

fiveprofiles.cpp permits each activation to be full or a union of earlier branches, since every prior union can be expanded. It prunes only by coordinate sign flips that preserve earlier activations. There must be at least twelve distinct branch signatures among the 32 directions: the twelve disjoint nonempty rejection sets cannot distinguish directions with identical signatures. This leaves 2,208 profiles. canonicalfive.cpp identifies signed permutations of the five bit coordinates, leaving 617. The final test is invariant under any such permutation and does not enforce the representative's particular physical order.

## Helper search

exact_five_helpers.cpp offers B and W, immediately charging the distinct W masks against the five-helper budget. It enumerates up to 5−|W| further masks by binary unions. Strict helpers may be sorted by number of elements and then numeric bit mask: a proper union always has more elements than either operand. Each genuine helper family is generated, even though W was provisionally offered before it was constructed.

For each library enumerate all nonfull strict binary unions. A receiver may not coincide with a branch or activation, by the previous reductions. If there are L distinct trace atoms its deficit has at most L−11 atoms. Drop deficits containing a smaller available nonempty deficit. Replacing one with its subdeficit preserves disjointness and preserves any required nonintersection with a dirty activation. Choose twelve pairwise disjoint remaining deficits and demand for each nonfull U_j that at least one chosen deficit misses U_j.

Starting from the full source only, repeatedly enable every switch whose activation is available and every named helper computable by a binary union of two available masks. The least fixed point verifies that all helpers W and all extra helpers coexist with the switches in some physical order. This test relies on no designated representative order. A true instance would still be converted to a physical circuit and checked on all Boolean inputs before being reported as a construction.

paired_control.py transposes the known 29-gate four-AND threshold tail of the 41-gate crown and embeds its masks in a five-coordinate cube with one unused selector. specific_bank.cpp invokes the same receiver and scheduling tests on its six helpers and returns acceptance.
