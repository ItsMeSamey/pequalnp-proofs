# Seven canonical signatures among nine point outputs require 19 point gates

Consider a residual separator whose point boundary includes the seven four-point target neighborhoods and two other arbitrary singleton signatures. The nine wires may have repeated signatures and different behavior on nonsingletons. At least **19 paid point-only gates** are needed, independently of the line-side signals or the mixed circuitry. In particular, any such separator with at least 15 mixed gates requires at least 34 residual gates.

## Raw witness check

For target neighborhood T and a two-point subset B outside T, take a residual positive at point p on its singleton line and a negative with that line active and point set n containing B. Require n to meet every other canonical neighborhood containing p. All line signals and all other canonical point signals on the positive are then dominated by their negative values. If the T output accepts B, it is also active on the negative. An extra point signal can prevent the resulting dominance only if its singleton signature contains p and avoids n. This necessity uses monotonicity on nonsingleton inputs and applies separately to each wire, even with repeated signatures.

Fix the first extra signature and discard the witness pairs (p,n) it could distinguish. For the second extra to distinguish every remaining witness, it must contain the union of the p and avoid the union of the n. Enumerating this subcube and then taking the union over B identifies the extra signatures for which T could escape off-pair rejection. Over all unordered choices of both signatures with repetition, exactly 32,979,201 pairs have zero potentially unsafe targets, 577,227 have one, and 2,100 have two. Every choice therefore gives at least five canonical outputs that reject all off-target pairs.

Run from this directory with the adjacent seed-obstructions decoder.

```sh
g++ -std=c++17 -O3 verify_pairs.cpp -o verify-pairs
python3 decode_witnesses.py | ./verify-pairs
```

The eight printed counts correspond to zero through seven potentially unsafe targets.

## Point-gate count

A charge for target T is a paid gate whose singleton signature is contained in T and includes at least two points. No primitive is charged. Different targets have disjoint charge classes since their neighborhoods intersect in one point. An exterior gate has signature contained in none of the projective lines. The free signatures each lie in a projective line.

The two-charge lemma for a fully protected target requires at least two charges. At equality, three distinct exterior gates have pairwise signature intersections equal to T. Indeed, a first charged OR has size at most two, and a first charged AND of size at least three must have dirty parents, each containing an outside point. Their AND accepts an outside pair (extending a singleton if necessary). Thus a second-charge protected output cannot be OR, and must be AND with a clean parent of signature T, the first charge. That first charge intersects two strict supersets of T; the other output parent must also strictly contain T. The three supersets' outside portions are pairwise disjoint, since a shared outside point together with an outside point of the third would be accepted. They are exterior and realize three distinct pairs for T.

Choose five protected targets and write q for the number of these using exactly two charges. Their charges contribute at least 15−q. Each of the other two targets has at least one charge. With h exterior gates, at least 17−q+h paid gates are needed, and 3q ≤ h(h−1)/2 because each exterior pair identifies its intersection. For h from 2 through 5 this implies h−q ≥ 2. For h=6, q=5 would partition the edges of the complete graph on six exterior gates into triangles. Its vertices have odd degree, so this is impossible. For h≥7 use q≤5. These cases yield at least 19 gates.

If h≤1, each clean AND of signature size at least two has a clean parent. Otherwise its two parents each contain the same two points in T and an outside point, and are therefore both exterior. They are distinct because the output is clean. A clean AND therefore never enlarges the largest previous clean signature. A clean OR has clean parents. Free clean signatures have size at most one, so the first charged gate for T has size at most two. The second has size at most three, since an OR can then use at most one distinct previous charge. Thus all seven four-point signatures require at least three charges each in this case.
