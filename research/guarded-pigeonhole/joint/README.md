# Joint affine queries and induced restrictions

Encode two split-apex terminal selectors and the three original core score bits as a point of F₂⁵. Every affine query of at most three independent rows tests whether its fiber meets the joint image. Every nonempty such fiber is a union of affine two-planes. There are 1,240 two-planes, each consisting of four distinct points with XOR zero. Two joint images give identical answers exactly when the unions of all two-planes in their respective complements are equal. Indeed a plane is disjoint precisely when it is contained in the certified-missing union. The criterion also compares complete projected ranges by checking each target.

## A pair with every three-row projection onto

A connected seven-vertex core has adjacency masks [112,56,120,6,7,7,5], the first three vertices on one shore and score columns [1,3,2,2,4,4,4]. Two degree-four apex neighborhoods are 54 and 86. The apex label is zero and the target is 5. The first graph has no solution; the second has the unique core witness mask 38 plus the apex. Use opposite split terminals and a private length-three path between them with zero auxiliary labels. Encode joint points as 8 times the binary terminal sector plus the score. The split images have holes {5,15,21,29} and {5,15,21}. They differ only at the desired point 29. Neither complement contains a two-plane, so every consistent rank≤3 query succeeds on both. Restricting to core mask 38 distinguishes them using the two-plane {29,25,15,11}. Run check.py.

## Arbitrary adaptive deletions with returned witnesses

The stronger counterpair has a connected eight-vertex core with shores 0–3 and 4–7, adjacency masks [176,16,176,96,7,13,8,5], and scores [0,0,3,1,0,0,4,0]. The original apex neighborhoods are 225 and 226, both of degree four. Its label is 3 and the target 5. The first graph has no model; the second has unique original witness 381.

For any retained set T of split graph vertices (including its terminals and path interiors), let J_i(T) be the joint image of assignments valid in input i and supported in T. Let K(T) be the image of the intersection of the two actual support families restricted to T. The three images give exactly the same rank≤3 occupancies for all 4,096 choices of T. Every positive query therefore has an identical full vertex-labeled witness legal in both graphs. An adaptive algorithm restricted to these oracle answers and arbitrary induced zero-deletions can be given the same transcript, even if it requests witnesses. The adjacency data themselves differ; this result limits the oracle interface.

It suffices to verify each native support x. If its score belongs to the projected closure of K(supp x), every query containing this score has a common witness contained in x and hence retained under every deletion that preserves x. Each side has 316 native supports, 38 exclusive. Every exclusive support has a common subsupport of identical joint score except support 893 in the second split graph. Its point is 30, and the common subsupport image omits 30 and exactly {5,6,13,14,20,23,28,31}. These latter eight form an affine three-flat excluding 30. The XOR of any three belongs to that same flat, so no missing two-plane contains 30. adaptive.py verifies this compact certificate and all 4,096 masks. The score coordinates must remain the two terminal bits and three original core rows. Adding a private selector row or pinning another selector to one can distinguish the pair.

An independent smaller construction has a six-vertex core with shores of size three, adjacency [56,32,24,5,5,3], scores [0,5,0,0,7,6], apex neighborhoods 3 versus 11, apex label 7, target 3. The first (degree two) has the unique full original support as a witness. The second (degree three) has none. Every proper core deletion even has identical full five-bit images. All 1,024 arbitrary deletions of the ten split vertices have identical rank≤3 projections with common witnesses. The first side has 144 supports and the second 124. Only support 255 on the first side lacks an identical-score common subsupport. Its joint point is 28 and the other eight holes of its common subsupport image are {3,4,10,13,19,20,26,29}, an affine three-flat excluding 28. small_adaptive.py independently checks this example.

## Classifying missing active points

Let H_j be the missing scores in each lower sector j=00,01,10 and U the attained 11 scores. A missing active point s is detected if and only if at least one of three conditions holds.

* The point lies outside the affine hull of U.
* There is a nonzero δ such that s+δ is also missing in 11 and δ is a difference between two members of some H_j.
* The point belongs to H_00+H_01+H_10.

Indeed, project a missing two-plane through (11,s) onto the two terminal coordinates. Rank zero means the whole plane is a missing affine score hyperplane within 11. Rank one means that the active slice and some lower slice each contain a missing pair with common difference δ. Rank two means one point falls in each sector and the XOR of the three lower scores equals s. These exhaust the possibilities.

A common nonzero neighborhood gauge h and arbitrary named deletions always reveal differences in apex incidence on a fixed labeled core. Retain just core vertex i, ask that both terminals vanish, and test one score character λ with λ(h)=1. The singleton can witness λ(score)=1 precisely when λ(L_i+h·1_{i∈N})=1. An adjacency change yields opposite responses.
