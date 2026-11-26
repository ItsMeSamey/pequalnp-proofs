# Four private guard groups at width twelve require twelve point gates

Consider twelve point-side boundary wires satisfying the L-meta-18968 raw point obligations. Suppose four different target neighborhoods have disjoint private groups among these wires: all group members accept the target's four singleton inputs, and for every two-point input outside the target at least one group member rejects it. Then the original point circuit needs at least **12 paid gates**. Repeated singleton signatures and redundant slots are allowed.

This is the width-twelve instance of the duplicate-tolerant interval enumeration in the companion four-private-groups and missing-line-nine certificates. Seven pairwise incompatible obligations distinguish seven slots, four belonging to different private groups. The remaining slots can be assigned any group role or no role. A group can retain a canonical target wire alone or use three or more proper supersets. The signatures of a three-wire group have pairwise disjoint outside portions. Larger groups require an outside-pair rejection witness for every pair. The enumeration covers all membership intervals, subject to these conditions and the 1,323 raw obligations. No assumption that a slot is necessary for raw separation is imposed.

The hereditary point lower bound projects onto every subset of target lines and grants transverse masks for free. It counts removable paid wires conservatively across uncertain or duplicate intervals, and credits target recovery from clean pairs, triples, full targets and group intersections. It uses the previously proved three-gates-per-retained-target theorem. Four completed canonical targets already cost twelve. The native program prunes only at a certified lower bound of twelve, then branches on unassigned singleton memberships. The five quartet orbits under the verified sample symmetries cover every possible quartet. The union of all symmetry images of the 31 free point inputs is granted, giving a 55-mask relaxation.

Run `python3 verify.py` from this directory beside four-private-groups. An optional argument supplies the path to that package. Verification uses Python 3 and a C++20 compiler. All five searches finished with zero surviving twelve-slot banks at budget eleven.

| Quartet orbit | Nodes |
|---:|---:|
| 15 | 228,607 |
| 23 | 86,153 |
| 27 | 90,893 |
| 46 | 208,315 |
| 83 | 923,641 |

At 20 mixed gates the exceptional nine-line read-once bank missing a singleton gives four such groups by the line-tree part of missing-line-nine, which is independent of the number of point occurrences. The point side costs at least twelve and the line side at least three, so that architecture costs at least 35 gates. For the adjacent ordinary two-pair masks the same result rules out any placement shown in the earlier line-tree proof to yield four groups: 20 mixed plus two line plus twelve point gates is at least 34.

At twenty mixed gates, twelve point and nine line wires make the mixed cone read-once. Each of the 24 missing-singleton banks has four private groups and needs three paid line gates, so its total is at least 35. [Line-tree proof](../missing-line-nine/README.md)
