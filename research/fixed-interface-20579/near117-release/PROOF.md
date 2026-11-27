# Five fixed ports and 117 specified donor banks

Cut terms 220, 223, 224, 225 and 226 of the 181-gate control. Trace wires 243 and 121 backward, stopping at the five ports. This retains 140 gates. Retain also marker 244, the NOT of 121, for a fixed physical charge of 141. The removed region contains 40 gates. Completion at size 170 therefore permits at most 29 replacement gates with five labeled taps. The marker may be read as an additional source. Its paid inversion is outside the replacement.

The final output ORs the five taps with the retained terms. Their contribution must be one on the 98 uncovered positive cells and zero on all 613 graph-zero cells. Write P and N for the signatures of these cells on a chosen bank. The other cells impose no condition on the contribution. The inputs actually traced by any valid completion must separate P from N, since the computation is constant on each projected signature.

## Family and separating size

The original region has 39 incoming wires. On this bank 31 coordinates have a positive/negative pair differing solely there. Retain these mandatory coordinates and enumerate subsets of the other eight by increasing size. The first separating subsets give six banks of total size 35. From each, remove two wires and add one wire outside that bank from the specified retained donor pool of raw inputs and paid gates. Keep the separating results and deduplicate identical wire sets. These are the 117 specified 34-wire banks. Grant marker 244 as an additional possible source in each. The old-tuple ranking and the number of reproducible old gates do not enter this bound.

For each augmented bank determine mandatory coordinates using the same opposite-label neighbor test. Enumerate subsets of the other coordinates by increasing size, projecting P and N onto each subset together with all mandatory coordinates. The first size admitting disjoint projections gives the exact minimum separating size S, since every separator must include the mandatory set and any disjoint projection supports a lookup function satisfying the forced labels. Record every successful choice at that size.

## Incidence count

Trace all observed available operands backward from the five taps. Let s count distinct traced donors, g all replacement gates and D dead gates. Let H sum two minus the available observed operand occurrences over live gates, plus one per unavailable tap. Let F sum use count minus one over traced producers, including donors, live gates, repeated pins and labeled tap uses. Each traced producer has a use. NOT observes only its first operand. A missing or forward wire contributes no producer incidence, an explicitly unavailable read denotes false, an absent AND/OR list entry is omitted from its fold, and NOT defaults a missing first entry to false. Counting incidences at producers and consumers gives
     
    (g−D) + s + F = 2(g−D) + 5 − H,
    g = s − 5 + D + H + F.

In particular s ≥ S. Where a forced-positive vector is coordinatewise below a forced-negative vector on the augmented bank, a completion must use a live replacement NOT. Otherwise all live gates and the tap OR are monotone on the donor coordinates, treating the supplied marker as a coordinate. This proves H ≥ 1. Such a decreasing witness persists on every separating subprojection.

## Direct wedges and fork count

For two donor coordinates x,y, a wedge consists of a promised center and two opposite-label promised neighbors differing solely in x and solely in y, respectively. The quadrant is the ordered pair of bits at the center. Join x and y by an edge in G if wedges occur in two distinct quadrants. A clique of size k proves F ≥ k−1, by the stronger inequality F ≥ χ(G)−1.

Indeed, join the taps with an analytical binary OR tree to give a single output. Each tap occurrence becomes a pin, preserving use counts. Assign each traced donor to the first producer with multiple uses on its unique forward path, counting the donor itself if it forks. Those reaching the root without a fork form one additional class. There are at most F+1 classes. Edge endpoints must be traced because a wedge contains a distinguishing pair for each coordinate. Isolated untraced vertices can be assigned any color.

Two distinct donors in the same class have unique paths up to a common stopping point. Their paths first merge at a binary AND or OR. Every earlier side operand is independent of both donors since neither donor has another path before the merge. Along each branch the polarity, when sensitive, is fixed by the parity of its NOT gates. All subsequent dependence on the two donors passes through the merge value, even if it later forks or is inverted. At a wedge center both branches must be sensitive, and each individual toggle must change the merge value. An AND merge requires both branch values one there, an OR merge both zero. The branch polarities thus fix the center quadrant in all contexts. Two distinct wedge quadrants force different classes. This properly colors G and proves the inequality, including forks at raw donors, taps, repeated pins and reconvergence.

The separating size, inversion and clique bounds charge different terms s,H,F of the identity. They can therefore be added. In particular a decreasing witness and a k-clique give g ≥ S−5+1+(k−1). The witnesses on a full bank apply also to a circuit ignoring any of its optional coordinates.

## Final projections

Using mandatory counts, the recorded decreasing witnesses and the full-bank cliques gives bounds 28, 29, 30, 31 and 32 on respectively 1, 9, 28, 36 and 43 banks. Substituting the exact separating sizes excludes 116 banks at budget 29. The sole remaining bank adds donor 112, has 31 mandatory coordinates, and has optional coordinates 52, 66, 100 and 244. The mandatory coordinates alone fail to separate. Exactly two singleton additions separate, namely 66 and 100. The full bank has both a decreasing witness and conflict edge (23,60). Tracing two or more optional coordinates therefore requires at least 33−5+1+1 = 30 gates.

At budget 29 the remaining choices have exactly 32 traced donors. Recompute the wedges on each exact projection, where coordinates omitted from the circuit need no longer agree between neighboring cells. Adding 66 gives the clique {24,66,81,112}, hence at least 32−5+1+3 = 31 gates. Adding 100 gives {23,60,100}, hence at least 32−5+1+2 = 30 gates. Both exceed the budget. Every replacement from a subset of one of these 117 augmented banks needs at least 30 gates with these fixed ports, giving a physical total of at least 171 with the 141 retained gates. The result is confined to this family, fixed cut and retained circuitry.
