# Irreducible families of ten point-boundary signals

The enumerator finds 1,218,270 unordered ten-signature families that meet every line-dominated raw separation obligation and cease to meet them when any member is removed. A gate-count bound and two refinements leave 23,274 families with point cost at most 16. Of those, 6,543 have point cost at most 15. These counts define the inputs to the separate one-copy and read-once mixed-circuit checks. Families that contain a smaller feasible basis are handled separately.

## Reproduction

From this directory run the following command with Python 3, a C++20 compiler supporting unsigned 128-bit integers, and GNU command-line utilities. Provide a writable output directory for temporary binaries and result data.

```sh
bash verify.sh /tmp/seventeen-replay
```

The runner decodes the pinned theorem statement, regenerates the obligation files, enumerates the irreducible families, sorts them to confirm uniqueness, computes the full histogram, and checks the digest of the refined output list. The main replay uses Python's standard library. The separate five-target theorem includes its own SAT verifier and dependency list under five-target/.

## Complete enumeration

A singleton signature records which of the thirteen positive singleton point inputs activate a point-side signal. Each of the 1,323 maximal raw obligations consists of a positive point a and negative point mask B, with the positive line vector contained in the negative line vector. Some signature must contain a and avoid B. A family is irreducible exactly when every member privately witnesses at least one obligation. A private obligation has that member as its sole witness. Consequently no signature repeats in an irreducible family.

Seven pairwise exclusive obligations furnish seven labeled slots, and three extra slots remain. Assign each anchor to its numerically smallest witnessing mask and sort the remaining masks in ascending order. Exclusivity prevents one mask from witnessing two anchors, so each unordered irreducible family has exactly one canonical labeling. For a partial assignment, each slot records mandatory and forbidden bits. An order violation is certified only if the minimum possible mask of the earlier slot exceeds the maximum of the later one. The corresponding anchor check applies only once an extra slot necessarily witnesses that anchor.

For each obligation and slot, the enumerator computes whether the slot can still witness it and whether the slot already necessarily witnesses it. An obligation with no possible witness kills a branch. An obligation with a single possible witness forces its bits in that slot. For every slot, discard obligations necessarily witnessed by another slot or impossible for this slot. At least one remaining obligation must eventually be private. Its positive and negative membership requirements common to every remaining choice are therefore forced. Iterate to a fixed point. The next undecided bit branches both ways, with all free bits eventually assigned. At a leaf all obligations have witnesses and every slot has a private witness. Printing sorted masks gives the unordered family. Traversal visits 20,057,115 nodes. The SHA-256 of the uncompressed output is 05973885a89ec022aa6f11fc5e06bcb04afc208beac56033b448f73bd63673bd.

## Point-gate lower bounds

For each of the 2,961 unreduced raw obligations, compute its witnesses in the family. A unique witness must reject the obligation's negative point mask: every other point signal active at the positive is already active at the negative, as is every active line signal. Monotonicity forces rejection of every two-point subset of that negative mask. For each four-point target T, collect the signals whose signatures lie in T and which are thus proved to reject all 36 pairs outside T. Add its four raw singletons. On the 16 subsets of T, compute the least number c(T) of those signals needed to cover T. At most c(T)−1 additional ORs yield a full output safe on all outside pairs. The seven-safe-target bound is 21 point gates, giving the lower bound 21−∑(c(T)−1) on the actual point gates.

| Bound | Families |
|---:|---:|
| 12 | 23 |
| 13 | 237 |
| 14 | 2,097 |
| 15 | 11,889 |
| 16 | 70,584 |
| 17 | 219,954 |
| 18 | 640,534 |
| 19 | 169,416 |
| 20 | 103,536 |

The lower rows through 16 contain 84,830 families. First, for any selection of n≤5 full target masks already present, grant every mask meeting each selected target in at most one point as an input. Replacing each paid boundary output of this kind by a free input removes at least one distinct gate. The selected target outputs still require 3n gates by the five-target theorem. Adding the count of distinct granted paid outputs therefore supplies another lower bound. Free primitive masks incur no charge.

Second, if the first bound from completion remains tight, its upper reconstruction yields exactly 21 gates for seven safe full targets. As point-equality.md proves, every paid gate in such a circuit belongs to one of seven disjoint OR trees, each on four distinct point leaves. Hence each paid boundary signature must lie in some target and any two overlapping paid signatures in a single target must be nested. Violation excludes equality and raises the completion bound by one. The code uses this test only if the five-target test did not already increase the bound.

After refinement the survivor counts by point budget are 23 at 12 gates, 237 at 13, 1,245 at 14, 5,038 at 15, and 16,731 at 16. The separate 17-mixed-gate tests use the 23,274 families within 16 gates when there are seven line-boundary signals and the 6,543 within 15 gates when eight line-boundary signals require a paid line gate. This enumeration and these lower bounds do not by themselves reject mixed circuits.
