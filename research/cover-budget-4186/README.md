# Cover budget for L-meta-4186

The issued negation asks for a nonempty four-cycle-free graph and a globally minimum, exact binary AND/OR circuit in top form for which the cover budget fails. No such witness was found. **Any remaining violation requires at least two dirty AND gates and at least three graph edges uncovered by the top stars.** The reviewed arguments exclude each smaller range independently. Whether a violation exists beyond those bounds remains open.

## Reviewed case analysis

Let τ be the minimum vertex-cover size, u the number of uncovered edges, t and c the numbers of noncentreless and centreless tops, j the number of junk AND gates, and q the number of non-lambda outside OR gates. Strict failure requires τ + u > t + 2c + j + q. Selecting a centre per noncentreless top and an endpoint per remaining edge gives τ ≤ t + u. For u > 0 there must be a junk gate, and the last junk gate has a reader forcing c + q ≥ 1. [Structural argument](cases/4186-audit.txt)

| Uncovered edges | Further conditions | Bound or argument |
|---|---|---|
| 0 | All | τ ≤ t. |
| 1 | All | j ≥ 1 and c + q ≥ 1 pay the two units in τ + 1 ≤ t + 2. |
| 2 | 2c + j + q ≥ 4 | τ + 2 ≤ t + 4. |
| 2 | j = 1 and 2c + j + q = 3 | A three-clause transversal gives τ ≤ t + 1. [One-junk argument](cases/4186-one-junk-transversal.txt) · [Centreless branch](cases/premises_4186_branch.txt) |
| 2 | j = 1, c = 0, q = 1 | The sole charged OR and the four-cycle-free star constraints give τ ≤ t. [Unique mixer argument](cases/4186-last-branch.txt) |
| 2 | j = 2, c = 0, q = 1 | Replacing a star centre with two endpoints gives τ ≤ t + 1. [Two-junk argument](cases/bounds_4186_two_dirty.md) |

These are mathematical case arguments. The hypotheses include global leastness, which permits removal of unused or redundant gates.

## One dirty AND, with any number of uncovered edges

With one dirty AND, its two operands are pure disjunctions with supports A and B. Every residual edge activates both disjunctions and meets the guard of an affected top. The resulting three-clause term has a pair graph coverable by at most two vertices. Sections of the proof use full-cube correctness on three active inputs. [Incidence classification](cases/4186-one-junk-incidence.txt)

If A and B overlap, their intersection is complete to the combined guard support. Square-freeness then restricts the guard structure, and counts of distinct pure OR gates and mixers pay for the residual edges. If the supports are disjoint, the residual edges lie on at most two pivot stars. Counting the charged gates in their operand cones and choosing centres to cover the pivots yields the same budget. Together these cases give τ + u ≤ t + 2c + 1 + q for every circuit under the one-junk hypotheses. Both arguments are mathematically reviewed and remain outside the kernel-checked scope. [Overlapping supports](cases/4186-one-junk-overlap.md) · [Disjoint supports](cases/4186-one-junk-disjoint.txt)

## A family attaining equality

Attach b and d pendant vertices to two distinct centres of a triangle, with b,d ≥ 1 and k = b + d. The displayed circuit has minimum size k + 4. Restricting each essential pendant to false saves at least one gate and leaves majority on three inputs, which needs four gates. The cover number is 2 and u = k + 1. Both sides of the budget equal k + 3. [Construction, counts and proof](family/bull-family.md)

The kernel-checked scope consists of three files. [BullLeast](family/BullLeast.lean) proves leastness for the five-vertex bull. [BullControl](family/BullControl.lean) verifies its displayed circuit, gate classes, cover and equality under its vertex labeling. [PendantLower](family/PendantLower.lean) proves the lower bound conditional on an essential-variable restriction chain ending in three-input majority. BullControl input labels 0,1,2,3,4 correspond to 0,3,1,4,2 in BullLeast. The general family's satisfaction of that chain and its exact gate-class counts are established in the mathematical argument.

## Finite search

The enumeration found no strict failure through five vertices. For six vertices without isolates, 25 of the 26 four-cycle-free graph isomorphism classes were reached at their minimum size through nine gates. The remaining class, canonical edge mask **5907**, was not reached through nine gates and remains open in this search. An isolated input cannot feed a gate of a least circuit. Setting it to false leaves the edge function unchanged, and the first gate reading it simplifies to false or its other operand. Propagating constants and retaining the original input labels would produce a smaller circuit. Graphs with isolates therefore reduce to smaller active vertex sets. Counts refer to the search's canonical encodings. [Five-vertex log](enumeration/connected_n5.log) · [Six-vertex log](enumeration/connected_n6.log) · [Small-graph counts](enumeration/small4186.json)

An independent run reproduced all ten completed layers and both full logs byte for byte. It used the hashed producer binaries after workspace memory limits and monitoring restrictions prevented a fresh independent build. A separate source review and an independent scalar checker reproduced every explicitly logged candidate. [Replay receipt](enumeration/replay.txt)

Run the following commands from this directory to verify the recorded hashes, exercise the generator, and repeat the finite search. The six-vertex run includes every size from five through nine.

```sh
(cd enumeration && sha256sum -c enumeration4186.sha256)
python3 family/pendant_family.py --test --checker enumeration/check4186.py
python3 enumeration/small4186.py
python3 enumeration/small4186_four.py
c++ -std=c++17 -O3 -DVERTICES=5 enumeration/connected_n.cpp -o /tmp/cover4186-n5
/tmp/cover4186-n5 4 8
c++ -std=c++17 -O3 -DVERTICES=6 enumeration/connected_n.cpp -o /tmp/cover4186-n6
/tmp/cover4186-n6 5 9
```

To repeat the three Lean checks, set RELEASE_DIR to this directory's absolute path and run from the lean directory of the [canonical project snapshot](https://github.com/open-goat/pequalnp-proofs/tree/624acb3fb2189a78719c262c1af407bd73fb3b5c/lean) with its helper modules built.

```sh
for f in BullLeast BullControl PendantLower; do
  lake env lean "$RELEASE_DIR/family/$f.lean" || exit 1
done
```
