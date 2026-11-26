# Ten point signals and eight line signals at seventeen mixed gates

Run `python3 verify.py` with a C++20 compiler named `c++` on PATH. All inputs are included. The checker decodes the SHA-256-anchored formal statement, reconstructs the 28 residual positives and 245 maximal negatives, compiles the checker in a temporary directory, and compares every batch total to its expected value. The positive control admits a separating tree.

SHA256SUMS pins the exact bytes shared with the sibling point-family enumeration and one-copy checks. refined-all.txt is the output of the irreducible-ten charge refinement. geom_reps.txt and dupgeom_reps.txt are the nonzero-distinct and zero/repeated representative outputs of extend-nine. The checker verifies those hashes before using the lists. The siblings justify their completeness and the sample-preserving permutations used in reduction. extend-eight treats smaller bases separately.

For 18 boundary wires and 17 mixed binary gates, the output cone is a tree and reads each leaf once. All positive samples have singleton point and line inputs. Replacing any side signal by the OR of its singleton signature preserves positives and can only decrease negatives. For eight line signatures the separate line-basis argument forces all seven raw singleton masks. The eighth line signal may repeat a mask or have zero signature. A line program with g binary gates has singleton support of size at most g+1. Thus a point lower bound c in a 33-gate circuit leaves at most 16−c line gates and permits eighth line masks of size at most 17−c. An eighth distinct wire costs at least one line gate. The checker applies the bound c≤15 to the irreducible list and grants *every* eighth mask to both extension lists.

If current leaf i is the only leaf that is true at a positive p and false at a negative n, then every minterm supporting p and every maxterm certifying n must contain i. Here a maxterm is a minimal set of leaves forced to zero to force the output zero. For a read-once monotone formula, every minterm intersects every maxterm in exactly one leaf. At AND, a minterm uses one minterm from each child, while a maxterm belongs to one child. OR gives the dual induction. Two leaves jointly mandatory at a positive and also jointly mandatory at a negative therefore contradict read-once separability. The positive and negative in this last test may come from different original witness pairs. The checker carries all eighth-mask possibilities as 128-bit sets. A positive-negative pair with no separating leaf rejects that possibility immediately.

For every surviving case, tree.cpp exhausts bottom-up merges. A merge can lose a positive-negative distinction only when exactly one replaced wire supplied the sole distinction. For intersection its partner must then be true on the positive, and for union the partner must be false on the negative. Both operations are checked, both kinds of mixed merges are allowed, and merges of two pure wires of the same side are excluded since this search begins at the boundary of the mixed cone. Memoization sorts the multiset of signatures on the sample including their point, line, or mixed ancestry. Multiplicities are retained. A semantic state produced by two different merge orders has the same possible continuations.

| Source | Families | Line-mask tests | Reach tree search | Separating trees |
| --- | ---: | ---: | ---: | ---: |
| Irreducible with point lower bound ≤15 | 6,543 | 252,005 | 0 | 0 |
| Nine-basis extensions, distinct nonzero masks | 1,713 | 219,264 | 0 | 0 |
| Nine-basis extensions with zero or repeated masks | 65 | 8,320 | 21 | 0 |

These three screens reject all 479,589 tested family/mask combinations.
