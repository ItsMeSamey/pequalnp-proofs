# Audit of selector order in four-, five-, and six-AND searches

A signed-axis quotient can choose a chronological representative in which two independent switches are ordered differently from the physical circuit. An OR-library restriction based merely on which of their coordinate numbers is smaller is insufficient. The following checks concern precisely this risk.

| Search | How order is handled | Audit |
| --- | --- | --- |
| Four-AND reverse budget, algebra/reverse/reverse_budget.cpp | Builds every chronological tuple, quotienting by XOR translation when selecting holes; activation decomposition grants late source masks | No post-permutation predecessor restriction |
| Four-AND final receiver check, selector_holes.py | Grants all eight branches, independent of time | Unaffected |
| Five-AND one-dirty, dirty_anchor_active.cpp | Exactly four full clean switches, followed by the only dirty split; the activation can use only clean sides | The clean switches can all be placed first; no ordering ambiguity among dirty switches |
| Five-AND one-terminal, singleterm_minimal.cpp | All paid W activations and branches initially granted | Unaffected |
| Five-AND two-terminal, twoterm_sym.cpp | Repeatedly considers all switches and all allowable unions until reachability stops changing | Least fixed point is equivariant under signed permutations |
| Five-AND all 617 classes, algebra/reverse/exact_five_helpers.cpp | Enables any switch whose activation is known and reattempts all five switches until no change; OR helper cardinality gives a dependency order independent of selector numbering | Complete generic ledger unaffected, independently verified by its author |
| Five-AND two-dirty formal pin reduction, reductions/twodirty | Raw templates keep the explicit chronological dependency as a distinguished formal input connection; legal axis isomorphisms preserve the two ordered demand rows, or exchange independent gates | No representative-index semantic precursor decision |
| Six-AND five-terminal | Only one dirty split, all five clean switches can be placed first | Unaffected |
| Six-AND one through four terminal, generic k=0 or k≥3 | No pre-split helper search | Unaffected |
| Six-AND one through four terminal, k=1 or 2 | The earlier solver chose a precursor library from the representative order. The corrected solver uses essential-dependence closure, or falls back to the wholly unrestricted helper search | The full case comparison is executable in six_causal_audit.js |

If activation V varies when selector j is flipped, V cannot be available before j's split in any physical order. This essential-dependence edge and its transitive closure are equivariant under all signed axis permutations. Therefore a demand can be granted sources from every split except itself and its forced successors, including splits incomparable with the demand in this partial order. Restrict those source masks to subsets of the demand. Grant each other paid activation in their OR closure too, independent of when it was produced. This is an overapproximation of every physically possible precursor library. If the originally selected heuristic demand has a different source set under this test, the repaired implementation omits precursor restrictions altogether.

For the main k=1,2 hard-hot-anchor cases, the old and causal source sets agree wherever the heuristic requested precursor work. The checker asserts zero fallbacks triggered by source differences on every such case for 1, 2, 3, and 4 terminals. The optional all-profile one-terminal cross-check had twelve one-paid and forty-eight two-paid exceptions; these are covered by the corrected unconditional fallback. The counts in the final corrected replay, rather than the historical optional subtotal, control its verification.

Both independent implementations reproduced the eight source-set comparison rows byte for byte in six-causal-ledger.ndjson. Corrected optional counts and original representative indices are in six-causal-corrected-optional.ndjson.
