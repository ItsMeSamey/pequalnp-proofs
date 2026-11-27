# Persistent signed variable with optional occurrence erasure

Use four seam labels G,B,P,N numbered 0 through 3. Fix feedback F with image array (0,2,3,1). Precede F by independently optional native rotations r=(0 1 2) and s=(0 2 3), composing as F r^a s^b, so that a signal encounters s first. The complete cycle table reads

| a | b | Good cycle | Bad cycle |
|---|---|---|---|
| 0 | 0 | G | B,P,N |
| 1 | 0 | G,P | B,N |
| 0 | 1 | G,N | B,P |
| 1 | 1 | G | B,N,P |

Inflate P and N by inserting the lists of positive and negative literal occurrences on their respective incoming wires. This traverses a whole signed bundle whenever its seam label is reached. Splice the local good cycles into one cycle by cyclically permuting all the G seam destinations; do the same at B in an independently chosen variable order. This joins the circuits without changing any local variable setting. Every physical setting now produces a partial assignment: each variable places all its positive occurrences, all its negative occurrences, or none on the good cycle. Each Boolean assignment is available. A variable placing neither sign on the good cycle may be completed with either truth value.

To erase occurrences independently, give each occurrence two consecutive sockets u,v inside its bundle and mark v. Give it a distinct socket w on a permanent bad segment. Put these w sockets in any prescribed order. Before the current routing p, optionally apply (u v w). Initially p(u)=v. In the new successor u goes to the old p(v), w goes to v and v goes to the old p(w). This cuts v out of its position and inserts it after w. The reasoning also applies if it was already on the bad cycle. The triples are disjoint. Their application preserves exactly two anchored cycles, and puts the erased occurrences after their own bad slots. Thus the possible good sets are precisely the sets of occurrences containing at most one sign of each variable. This is the feasible set of arbitrary subsets of true occurrences across all assignments.

Surviving good occurrences retain their order within the chosen sign bundle, and the good bundles retain the chosen variable order. On the bad cycle, the slots for erased occurrences have a free order. The surviving signed bundles still follow the local table, including the reversal between the two neither settings. These order restrictions matter for any detector sensitive to the boundary permutation. Splicing two local G and B rings does not itself permute surviving good occurrences into an arbitrary clause order.

The whole-socket checker uses two differently ordered variable rings and nontrivial bad-slot orders. Its two examples exercise 256 and 2,048 physical settings respectively, with 9 and 20 distinct attainable good sets. Each case exhausts the claimed feasible sets. Both cases trace both anchored cycles and check that together they contain every socket.
