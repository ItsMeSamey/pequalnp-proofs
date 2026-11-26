# Lower bound of 32 binary gates for the normalized live residual of L-meta-18968

Let s be the number of binary monotone gates, n the number of distinct live raw inputs, and k=s+1−n the number of outgoing uses above one. The prior size31-lower certificate proves s≥31 and incorporates the physical live-circuit threshold k≥10 for s≤33, proved independently for the seed-deleted residual. The raw input comparison tests force every one of seven line flags and twelve singleton point inputs. At least one optional must be selected to hit each of {2,3}, {2,6}, and {2,258}. This gives n≥20.

Assume s=31. Then k≥10 implies n≤22, giving exactly three cases.

* At n=20, k=12 and the unique bank consists of all thirteen singleton point signals and all seven raw line flags. The size31-n20 proof excludes every number of original recoverable ordinary labels.
* At n=21, k=11. With just two optional primitives, raw mask 2 is necessary, and there are 18 choices for the additional composite. The n21 archive exhausts these physical banks and all possible counts of mandatory owners. The five physical bank representatives are related to the remaining banks via permutations checked on the full signed table.
* At n=22, k=10. Three optional primitives are available. If mask 2 is present, two different composite inputs can be chosen in 153 ways. If it is absent, the only option is {3,6,258}. All seven mandatory owners are forced by the nested ten-excess supplier certificate and the zero-single/single-helper proofs in size31-lower.zip. The size31-n22-complete replay covers all 154 physical banks.

These are disjoint and exhaustive cases for s=31. Hence every normalized residual needs at least 32 gates. The included 34-gate circuit supplies the upper bound. Run python upper34/check.py to audit every operand and evaluate all 676 rows against the exact statement, including its compulsory seed. Size 32 and size 33 remain open. The separate necessary table of 246 (mixed gate count, point width, line width) triples at budget 33 remains in effect.
