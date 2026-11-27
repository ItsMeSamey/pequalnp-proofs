# The unrestricted minimum for threshold two on eleven inputs is 27 gates

The circuit model has unbounded fanout, arbitrary depth and binary monotone AND and OR gates. Threshold two accepts a Boolean vector precisely when at least two inputs are true. The explicit circuit in `control27.json` uses 27 gates, including four ANDs. The evaluator `control.py` tests all 2,048 assignments.

## Lower bound

The existing unrestricted lower bound is 26. Assume a 26-gate circuit exists. Choose a minimum-size representative, minimizing its AND count and then its singleton-positive (dirty) AND count within those constraints. The clean-terminal collection and direct-minor reductions preserve threshold, weakly decrease AND count and preserve or decrease size. A direct raw receiver would give a circuit on ten inputs with at most 23 gates after specialization, contradicting the ten-input minimum of 24. Each raw has exactly two OR readers: one-use cases and twice-used inputs feeding an AND permit an extra saving or contradict clean-terminal minimality. Let A be the actual number of AND gates.

| Actual AND count | Exclusion at 26 gates |
|---|---|
| At most six | The published six-switch certificate establishes a minimum of 27 under this restriction. |
| Seven | The signed-branch and physical-continuation cases below exhaust the normalized circuits. |
| Eight | The circuit has exactly 18 ORs. Pure OR groups, their incidence graph, and the star and component inequalities give the contradiction in `eight/eight-and.md`. |
| Nine or more | The physical OR floor is 2·11−4=18. This leaves room for at most eight ANDs. |

## Seven actual ANDs

Cut the gates into their two signed inputs and transpose the OR wiring. A 26-gate candidate yields at most 26−11+1=16 binary unions. The eleven distinct nondirect raw receivers are incomparable paid sinks, leaving at most five other paid unions. Every singleton has a nonempty rejecting set of selector directions. The eleven sets are pairwise disjoint, since every pair must be accepted. Clean-terminal collection attaches all singleton-negative AND outputs directly to the final OR collector. At least one AND must be clean: otherwise each input to the collector would be either a raw, an OR of raws or a singleton-positive AND signal and the output would be true on a singleton. Let d be the number of dirty ANDs.

| d | Exhausted classes | Source and argument |
|---|---:|---|
| 0 | Four widths | The eleven disjoint cubes require maximum width 4 through 7. Direct raw receivers were excluded. `low-dirty/general11.cpp` enumerates anchor trees, shared helpers and pairwise-conflicting available receivers. Its legacy budget 17 encodes five nonreceiver helpers as 17−12. |
| 1 | Six continuation widths | The single nonempty consistent continuation is a union of signed pins of the six clean comparators; independence of pin signs and comparator permutation leaves six widths. `low-dirty/seven26.cpp` enumerates semantic helpers and packs eleven disjoint deficits. The universe uses 128 directions. |
| 2 | 68 physical templates | `seven/two-dirty.md` describes protected-continuation synthesis, the opposite-pin requirement and the exhaustive physical helper checker. |
| 3 | 1,154 physical templates | `seven/three-dirty.md` partitions these into pin-budget, matching, two-tag and general helper classes. |
| 4 | 14,347 physical templates | `seven/higher-4/verified.out` gives exact IDs by case. |
| 5 | 105,791 physical templates | `seven/higher-5/verified.out` gives exact IDs by case. |
| 6 | 313,318 physical templates | `seven/six/verification-6.out` gives exact IDs by case. |

The one-dirty continuation cannot contain both sibling pins of one clean comparator: in the reversed graph their union equals the entire clean comparator activation, making the continuation full and permitting reclassification as clean. When d≥2 the general template enumeration retains chronological physical continuation masks before quotienting simultaneous pin swaps and comparator relabelings. Every earliest dirty comparator needs shared incoming wires carrying its opposing pins separately. If c is the simultaneous cost of its protected continuations and e counts earliest dirty roots, the resulting pin budget is c+e≤5. The matching-equality and two-tag cases are justified in `lemmas/higher-matching.md`, `lemmas/two-tagged-helpers.md` and `lemmas/straddler.md`. The physical signed-half filter for d≥4 uses the ten-input minimum and applies to genuine switches as described in `seven/higher-dirty.md`. The proof uses the eight-AND and seven-AND cases only at their actual arities.

The final finite validation reconciles each unique physical row with exactly one analytic or computer-tested case. No admissible eleven-receiver packing remains. The exact upper and lower bounds agree.
