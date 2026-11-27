# Flat signed normal forms with dictionaries on fixed supports

With the fixed 115-gate split25 prefix for L-meta-20579, shard 53, a flat signed DNF with a free dictionary of **all Boolean functions on each of two fixed pairs** requires at least **57 additional gates**. With a free dictionary of **all Boolean functions on one fixed triple** it requires at least **59 additional gates**. The 170-gate cap allows 55. The same counting method gives CNF tail bounds of 40 and 41, respectively, which leave the corresponding CNF cases open.

Each dictionary supplies every Boolean predicate on its designated original prefix ports, including complements. The two pair supports may overlap or coincide. In that family each free predicate depends on one designated pair. A signal that jointly depends on both pairs must be built within the stated flat representation. In the triple family the dictionary already includes the output of every cascade whose resulting function depends only on that triple, regardless of its internal depth. A single free dictionary on one fixed pair has lower bounds of **82 tail gates for DNF and 58 for CNF**. The [baseline proof](baseline/README.md) gives the single-pair fiber counts and the physical model of old literals, binary gates, and sharing.

## Replay

The package includes a byte-for-byte copy of the baseline checker, manifest, public statement, and both packing certificates in the baseline directory. The extension checker uses only these local files and Python 3.10 or later.

```sh
python3 -I -B check.py
```

The checker validates its checksum manifest and runs the baseline checker. That reconstructs all 1,024 labels and 25-bit signatures, verifies the 18 distinct decreasing coordinates, and checks all pairwise blockers in both packings. It then enumerates 45,150 unordered pairs of two-coordinate supports with repetition, and 2,300 three-coordinate supports. For each family and normal form it reports the worst packing lower bound and a minimizing support choice for each overlap count.

## Why the packings survive

For two pair dictionaries, fix one coordinate of each support. If both choices pick the same port, fix it only once. For one triple dictionary, fix two of its three ports. On the resulting fiber, every predicate from any one dictionary is a unary function of the same remaining coordinate for that dictionary. Consider two packed cells in such a fiber and their recorded opposite-label blocker. The blocker shares the fixed bits. For any dictionary predicate on which the two points agree, either the remaining input agrees as well, or the restricted unary function is constant. In either case the blocker shares that predicate value. All signed literal agreements used in the original packing proof therefore survive.

For each support choice, the checker selects the largest packing fiber over the eligible fixed coordinates and all assignments to them. Let d count the 18 decreasing coordinates that belong to the union of the dictionary supports. The DNF packing minima by d are as follows.

| Dictionary supports | d=0 | d=1 | d=2 | d=3 | d=4 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Two pairs | 31 | 28 | 27 | 25 | 23 |
| One triple | 32 | 27 | 25 | 23 | — |

## Counting productive units across a whole dictionary

Consider all unit DNF terms drawn from a single dictionary in a proposed exact formula. Their union is one Boolean predicate on that same support. It is false on every target-zero cell because each unit term is individually safe. On the selected fiber it is unary. If two packed positives were covered by any units from this dictionary, their negative blocker would also satisfy the union by the unary argument above. Hence **all units from one dictionary together cover at most one packed positive on the fiber**. For CNF, take the union of the falsification regions of all unit clauses drawn from one dictionary. It is false on every target-one cell, so the same argument limits it to one packed negative. The bound applies to any number of units, including the entire dictionary. If the two supports coincide, counting two dictionaries only weakens the result.

Let k be the packing size on the selected fiber and q the number of designated dictionaries. No old unit literal can serve because both values occur in both target classes. At most q packed points can be handled by dictionary units. All remaining packed points require distinct nonunit term or clause outputs, since the pair blockers agree with every shared augmented literal. These outputs require at least k−q binary gates. Combining k distinct outputs takes at least k−1 binary gates of the opposite operation. On each of the 18−d decreasing coordinates outside all dictionary supports, every dictionary predicate has equal values at the endpoints of the directional witness. The flat expression must use the negated old coordinate to realize the decrease, costing a distinct unary gate. This gives 2k−1−q+18−d tail gates with every dictionary predicate free.

The same counting argument for q=1 on a single pair promotes the baseline packing computation to a full dictionary bound. Its DNF fiber minima for d=0,1,2 are 39, 38, 34, and its CNF minima are 21, 23, 24. The resulting minima of the gate expression are respectively 82 and 58.
