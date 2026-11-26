# Thirteen-input threshold two with at most five ANDs

The 32-gate grid-splitting control uses five AND gates and is checked on all 8,192 assignments by two independent representations: scalar wire lists and one bit-parallel truth table. A size-31 circuit on thirteen essential inputs has at most 31−13+1=19 reverse unions. A direct receiver would specialize to a size-28 circuit on twelve inputs, ruled out by the exact lower bound of 29. Choose a size-minimal, then minimum-dirty counterexample. Thirteen distinct raw receivers are paid sinks, leaving at most six other unions. Every distinct nonfull activation that is not a branch is a separate paid helper. A receiver is not contained in a free branch or a mandatory activation: one could enlarge it to obtain a direct circuit or cancel a dirty activation. See prior ten- and eleven-input transfer proofs and the arity-independent cancellation statement.

Fewer than four AND gates have fewer than thirteen resolution words and cannot supply thirteen disjoint nonempty rejection events. For four switches inputs.py directly enumerates all gate activations as full or unions of earlier branches, and canonicalizes under all four signed-coordinate permutations. For five switches it filters the independently recomputable 703-orbit five-switch corpus used in the ten-input proof. Keeping observable joint branch partitions with at least thirteen atoms respects signed equivalence. This leaves six four-switch orbits and 564 five-switch orbits.

If a dirty activation omits at most two trace atoms, no minimum-dirty solution exists. Any proper hot receiver contains the activation, and either equals it or, if it adds one of two atoms, lies in the activation union one of its own branch constituents that distinguishes the required atom. Such hot receivers can all be redirected to an activation and at most one branch, cleaning the gate without increasing total gate count. This leaves one four-switch and 67 five-switch orbits. The five-switch counts by q, the number of six helpers remaining after charging mandatory activations, are 18,26,16,7 for q=3,4,5,6. The four-switch all-shapes replay additionally dispenses with the sparse cutoff.

The search tests every helper family of size at most q in increasing population-count then numeric mask order. A preliminary anchor is either a minimum-deficit raw (at most floor(L/13) observable atoms, where L is the observable-atom count) or a required hot raw which cannot be redirected to one older dirty activation and a single branch. Helper strict subsets of the anchor may be formed before all other helpers, since no outside mask can feed such a subset. A strict supermask helper cannot be needed: it could neither feed any other raw receiver, by incomparability, nor reach a nonfull activation in this normalization. The final test enumerates twelve additional raw sinks, each available as one final binary union and each having a proper nonempty deficit disjoint from the anchor and all other deficits. The full orientation tuple is preserved under each signed orbit action in low.js, including the signed permutations of the physical branch expressions. minimum.js uses only minimum-volume anchors and permits sparse profiles.

The complete five-switch ledger low5.tsv has 67 distinct nonsparse orbits, 45,729,068 tested anchored libraries and zero packings. Orbit 396 accounts for 19,774,388 libraries. The independent chronology-sensitive C++ solver checked every one of the 18 three-mandatory-activation orbits, totaling 516,517 libraries and no hit. The four-switch all-shapes replay used 408,527 libraries. The ledger checker verifies IDs, reconstructs observable-atom counts, and recomputes totals independently. Combined with the 32-gate five-AND control, the minimum over all thirteen-input threshold-two circuits with at most five AND gates is exactly 32. Larger AND counts require separate arguments.

To replay, compile profiles.cpp and canonicalfive.cpp in C++20 mode. Pipe the former program's stdout through the latter and compare against five-universe.txt. From the package directory run the following commands.

```sh
python3 inputs.py
node minimum.js all4.txt > full4-min.tsv
node low.js hard4.txt > low4.tsv
node low.js hard5.txt > low5.tsv
python3 audit.py
python3 check32.py
python3 verify.py
```

The JavaScript enumerators accept any nonempty subset of the indexed input rows. Concatenating disjoint shard outputs gives the same per-orbit count and hit flag.
