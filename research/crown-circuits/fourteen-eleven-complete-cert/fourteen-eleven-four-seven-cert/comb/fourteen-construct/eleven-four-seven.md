# Eleven flags, two components of orders four and seven

The ten-to-eleven extension of the four-flag argument assumes an eight-AND host with at most seventeen decoder gates and nine decoder ORs. For a connected four-vertex component with r edges, the other component has 14−r edges on seven flags. The possibilities are r=3,4,5,6.

A four-vertex diamond or K4 has two universal vertices. For each universal, if adding its flag to every negative large edge were still negative, pin it to one and introduce three independent virtual raw inputs on its star edges. A nonempty virtual assignment has exactly its true graph flags; with no virtual assignment the real singles still reject and real pairs still accept. Pinning the essential universal removes at least one gate. For eight real edges, the seven flags cost 16−7=9 ORs and the decoder then costs at most sixteen gates, contradicting C(11)=27. For nine real edges the bank costs eleven gates, contradicting C(12)=29. Both universal vertices thus spoil some negative edge, and four-flag-three-lost-ors.md forces at least four decoder ORs to disappear with the small component. This contradicts any certified six-OR floor on the large component.

For a four-vertex tree or unicyclic shore one instead uses the earlier physical four-flag remote proof in degree/t14-34/eight-and-four-vertex-remote.md, under its stated regular eight-AND flag roles. Its role argument after the initial quartic-center reduction requires only that erasing the four-flag shore cost at most three ORs, guaranteed by the same six-OR floor.

Reading degree/t14-34/eleven-atlas.tsv gives:
- 3+11 edge split: 118 rows, all with six-OR floor on the seven-flag component.
- 4+10: 158 rows, all with six-OR floor.
- 5+9: 79 rows, all with six-OR floor.
- 6+8: 56 rows, 52 with six-OR floor.

Hence these two routes exclude 407 of 411 atlas pairs. The four residuals are K4 (G18) paired with seven-vertex G446, G447, G448 or G450. Each of those L graphs has eight edges and degree multiset 3,3,2,2,2,2,2, and the supplied OR lower bound is five. A decoder on these graphs still needs at least ten gates on L: its nine-gate flag bank and the decoder compute T₂ on eight independent raw edges, for which the known minimum is nineteen. Combined with the seven-gate K4-local bound, the local minima sum to the entire seventeen-gate allowance. Consequently the shared-gate counting obstruction of 507-bilateral.md transfers unchanged: every gate bypassed in both projections requires another gate actually surviving both.
