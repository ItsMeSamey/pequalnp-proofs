# Two raw lines each used twice

Combine this finite lemma with ../one-surplus/parallel.md. The outer tree has five ordinary raw lines and twice each of T,U. Let C be the OR of the side formulas at OR attachments in the ordinary skeleton and let b be the number of its point occurrences. Its unit-special cofactors C_T,C_U accept the four incident singletons of their own line and reject every exterior pair by the extension argument in parallel.md. C_0 rejects every singleton. If b≥6, one can instead build the two four-point stars directly with six additional point gates. For b≤4 use ../one-surplus/prune4.py. It suffices to compute both pair-safe outputs in at most five gates when b=5.

### Replay

Run the following in this directory using C++17 and Python 3.

    g++ -std=c++17 -O3 triples.cpp -o triples
    ./triples > triples.txt
    g++ -std=c++17 -O3 all.cpp -o all
    ./all > reachable.txt
    python resolve.py
    python geometry.py
    python check_geometry.py

The final check imports the sample decoder and raw JSON from ../one-surplus. triples.cpp enumerates triples (z,a,b) of Boolean truth tables on five independently labelled point leaf occurrences, using T and U each zero, one or two times, and evaluating all expressions at line settings (0,0), (1,0), (0,1). Recursive partitions combine arbitrary child formulas under AND and OR. Ordering the two child count tuples only fixes commutative symmetry. Assigning contiguous variable intervals to the children relabels the five occurrences and loses no unlabelled tree. all.cpp enumerates ≤5-gate monotone programs on the five point inputs and constants. resolve.py seeks simultaneous lower replacements for a,b with a and b preserved whenever z=0. It verifies 20,038 of 20,099 triples.

### Using the actual point signatures

Each of the two stars has three exclusive incident points and one common point. An exclusive T point must have a five-bit vector in the a=1,b=0,z=0 region. Lower that vector to a minimal vector in the same region. The chosen positive point still dominates the lowered vector. The three exclusive points determine between one and three distinct such vectors. Two chosen vectors v,w from two T-exclusive points satisfy b(v OR w)=0 because their point union is an exterior pair for U. The analogous condition holds on U's side. The common point dominates a minimal vector in a=b=1,z=0. geometry.py enumerates these possibilities and searches for lower replacements that preserve just the selected vector upsets, with 150 configurations considered and 33 remaining. The filter is necessary on all true configurations. If the common-point region is empty, there is no such configuration.

### Completing the 33 configurations

In each remaining case one label, say T, has a single vector v for all three exclusive points. The opposite label has one or two vectors. If two, pick a majority vector w dominated by at least two of its three exclusive points. At most one U-exclusive point requires a separate literal. In every case v and w are incomparable, and their Hamming distance plus one if a separate literal is used is at most five.

For the T output take the conjunction of point leaves in v minus w and OR the raw T/U intersection point. Every T-exclusive singleton passes that conjunction. If an exterior pair X passed it, select a side attachment whose T-cofactor is true on v, which exists because a(v)=1. Fix any ordinary neighborhood V resident there. The raw table has a T-active negative extending X, meeting V, and containing at least one of any two prescribed U-exclusive points dominating w. On this negative all coordinates of v minus w are true from X, and those of v intersect w are true from the U point. The side formula passes, and every ancestral AND guard passes via V, contradicting rejection. Thus the new T output is pair-safe. For U use the symmetric conjunction on w minus v plus the intersection literal and the optional single exceptional U-exclusive point. Its safety follows using any two of the three T-exclusive points. The gate count is the Hamming distance plus the optional extra literal, as checked above. Adding actual raw points of the target can never accept an exterior pair.

The 33 configurations split as 27 with one vector for both labels and six with one versus two. check_geometry.py checks every incidence, the needed negative extensions and both choices of majority. Thus all two-raw cases have the claimed five-gate reconstruction. No exhaustive search over the full 33-gate circuit is asserted here.
