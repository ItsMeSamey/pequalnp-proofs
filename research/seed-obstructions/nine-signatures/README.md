# Nine point signatures for a 33-gate residual separator

The enumeration partitions possible unordered multisets of nine point-boundary singleton signatures into three classes. One contains all seven canonical four-point neighborhoods. Another contains one of the 202 noncanonical eight-mask families. The remainder contains exactly 16,924 irreducible nine-mask families, where irreducible refers only to containing neither type of smaller signature cover. The two earlier classes can overlap. This directory verifies the enumeration and the lower bound of 18 paid point gates for every extension of one of the 202 families. The canonical case and the subsequent filtering of the 16,924 families have separate proofs.

## Reproduction

Run the following commands from this directory with Python 3 and a C++20 compiler.

```sh
python3 verify_eight.py
python3 inputs.py
c++ -std=c++17 -O3 enumerate9.cpp -o /tmp/enumerate-nine
/tmp/enumerate-nine < raw.in > /tmp/enumerated-nine.txt
cmp /tmp/enumerated-nine.txt nine.txt
python3 audit_nine.py
python3 supersets.py
```

The raw source is the SHA-256-pinned formal statement of L-meta-18968. For each residual positive with singleton point a and negative with point set b, keep the obligation (a,b) when the positive's primitive line vector is contained in the negative's. Some point signal must contain a in its singleton signature and have a signature disjoint from b. The 2,961 distinct raw obligations have 1,323 maximal b values across the point groups. These maximal obligations suffice for enumeration. The seven pairwise exclusive obligations give seven distinguished slots. Every feasible family can be numbered so those slots witness the designated obligations, including when another slot can also witness one. The other two slots are unrestricted. Equal signatures are allowed.

The enumerator tracks required and forbidden membership bits for each slot. An unsatisfied obligation with no compatible slot kills that branch. With exactly one compatible slot, the obligation forces the positive and negative membership bits of that slot. Otherwise branching assigns both values of an undecided bit. If all obligations are already satisfied, remaining unassigned bits are still enumerated. A branch is pruned as soon as completed slots include either all seven canonical masks or a known eight-mask family. Completing and sorting every remaining assignment yields all irreducible families. There are 3,870,973 search nodes, 76,824 complete slot assignments, and 16,924 distinct sorted families. The SHA-256 of nine.txt is b4a2755543b874f87b00321f803d63a900cef24876bcc0c445cd5020407f7479.

## One extra mask on an eight-mask base

Each of 175 bases replaces one neighborhood by two proper subsets whose union is the neighborhood. The other 27 bases split a shared singleton out of two or three neighborhoods, leaving a three-point remainder for each. For a target T, test the full output when present, both proper subsets in the one-split case, or its three-point remainder in the shared-singleton case.

Fix a pair B of points outside T and a designated output m. Consider all raw obligations (a,b) such that B is contained in b and m is the unique signature in the base containing a and avoiding b. If m accepted B, monotonicity would force it to accept b. The other base outputs and all line signals are dominated on the underlying positive-negative pair. To prevent this contradiction after adding signature x, x must contain a and avoid b for **every** such obligation. Thus x must contain the union of all required singletons and avoid the union of all forbidden b. The verifier enumerates that subcube, then unions the affected targets over all B and tested outputs. The table counts a base and its extra signature as an ordered choice, including repeated signatures.

| Missing canonical targets in base | No potentially unsafe target | One potentially unsafe target |
|---:|---:|---:|
| 1 | 1,404,170 | 29,430 |
| 2 | 169,962 | 2,070 |
| 3 | 48,552 | 600 |

No extension has two potentially unsafe targets.

## Point-gate count

A charge for T is a paid gate whose singleton signature lies in T and has at least two points. The charge classes are disjoint, since different projective lines meet in one point. An exterior gate has a signature contained in no projective line. Every free point signature lies in one of the projective lines, and intersects each of the seven residual target lines in at most one point unless it is a singleton.

A pair-safe output rejects every two-point input outside its target T. A first charge made by OR covers at most two points. If a first charge is made by AND, both operands contain an outside point, so their AND accepts an outside pair (extending a singleton if necessary). A pair-safe full target therefore needs at least two charges. At equality the output cannot be OR, since its first charge would have to be safe and contain at least three points. A final AND must have a clean operand with signature T. That operand is the first charged gate and itself intersects two strict supersets of T. The other output operand must also strictly contain T, since reusing the first charge cannot repair it. The three supersets have pairwise disjoint portions outside T; otherwise two outside points activate all three operands. They are distinct exterior gates, and their three pairwise intersections equal T. For q safe full targets with two charges and h exterior gates this gives 3q ≤ h(h−1)/2, since each pair identifies T. A pair-safe three-point target needs at least two charges by the first-charge argument.

For a one-split base, append one OR of the two proper components. The result supplies all seven full target masks, with at least six pair-safe outputs. Six safe full targets and the seventh mandatory full charge use at least 19−q+h gates. If 19 gates were enough, h≤q≤6. For 1≤h≤6 the pair inequality forces q<h, so h=q=0. A single charge cannot then make the seventh full target: an OR covers at most two points and an AND needs two exterior parents. Thus 20 gates are necessary after appending and at least **19** beforehand.

For r=2 or 3 shortened targets, at most one target loses pair safety. Counting three charges per full target and two per shortened target gives 21−r, before subtracting q and a penalty of at most two for the unsafe target, which still needs one charge. When h≥2 and q≤7−r≤5, one has h−q≥2. For h=2 through 5 use the pair inequality; for h≥7 use q≤5. At h=6, equality q=5 would partition the edges of the complete graph on six vertices into five edge-disjoint triangles, which is impossible because all six degrees are odd. Thus exterior gates compensate both penalties. When h≤1, an AND with a clean signature of size at least two must have a clean operand: two dirty operands would be distinct exterior gates, because each contains two points of T and an outside point. A clean AND cannot increase the largest available clean signature. A clean OR starts from primitive signatures of size at most one, and with just one earlier charge its output has size at most three. Hence every full target needs three charges and every triple needs two even without pair safety. The resulting lower bounds are **19** gates for r=2 and **18** for r=3.
