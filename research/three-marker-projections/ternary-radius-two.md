# Isolated accepting ternary words are globally unique

Take a closed permutation network with arbitrary fixed wiring, two marked physical wires, and independent ternary sites with all three cyclic rotations of their three sockets. If a successful word has no other successful word at ternary Hamming distance one or two, it is the only successful word. Deterministic subdivisions carrying the marks make them distinct from controlled departures without altering orbit membership.

Use the successful permutation itself as reference. Every single-site nonzero update must split the two marks. Two of its three departures therefore lie in the two different marked intervals on the common root circle; otherwise the untouched interval retains a directed path between marks. They cannot all lie on that circle: one of the two nonzero rotations agrees with its cyclic first return on the three sites, and its square retains the whole circle. Consequently each site has one cut u on the first interval, one cut v on the second, and a third cut w on an outside circle.

For two sites i,j order u_i before u_j. Say their chords cross if v_i comes before v_j in traversal of the second interval; otherwise the chords nest. The following exact local check counts, among four nonzero paired updates, those preserving the mark join.

| Outside circles | Crossing | Nested |
|---|---:|---:|
| Distinct | 4 | 0 |
| Shared | 2 | 1 |

For verification retain only the marks 0,1 and the two triples (2,4,6),(3,5,7). The base root circle is (0,2,3,1,4,5) if crossing and (0,2,3,1,5,4) if nested. The remaining base circles are (6)(7) or (6,7). Apply both orientations of each triple before the base permutation and follow the orbit from 0. Suppression of all other departure segments preserves the test; no independent lattice or surface assumption is involved.

Thus all outside circles are distinct and all root chords are pairwise nested. Under any nonempty set of updates, suppress each of its outside circles after applying the local rotation. Either orientation then has the same effect on the original root sites, namely the transposition (u_i,v_i). For the changed site whose u_i is first along the first interval, v_i is last among changed sites on the second. The path from mark 0 reaches u_i, takes the old successor of v_i and returns to 0 without reaching mark 1. This proves uniqueness for any number of sites.

In particular any acceptance language of minimum distance at least three, after fixing all non-trit choices, has at most one word. A template with these ternary input sites and h independent existential binary auxiliaries cannot faithfully recognize such a language of size greater than 2^h. For a full-rank ternary syndrome matrix on n nonzero, pairwise nonproportional columns, a fixed syndrome fiber has size 3^(n-r) and minimum distance at least three (unless it is a singleton). Hence at least ceiling((n-r) log₂3) auxiliary bits are needed in this interface. In particular the four distinct ternary directions in dimension two require at least four auxiliary switches for a singleton syndrome, since its nine ternary input words must have distinct auxiliary witnesses. No exclusion for polynomially many auxiliaries follows. The result assumes each logical trit is represented by one ternary rotation and both nonidentity alternatives are available.
