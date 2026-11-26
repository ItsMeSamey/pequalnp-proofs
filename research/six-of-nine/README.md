# Exactly six canonical neighborhoods among nine point-side wires require 18 paid point gates

Suppose a residual separator has nine point boundary wires. Six distinct canonical four-point neighborhood signatures occur, and the seventh is absent. Then at least **18 paid point gates** are needed. This excludes the case of 16 mixed gates and eight line boundary wires under a total budget of 33, since an eighth distinct line-side wire also costs at least one gate.

## Raw obligations and enumeration

Fix the omitted neighborhood. On any required singleton-point positive (p,l) and negative (n,k) with l contained in k, every line signal on the positive is dominated at the negative. If, for each of the six fixed signatures S, either p lies outside S or n meets S, its corresponding boundary value is also dominated. Some one of the other three boundary signals must distinguish the rows. Its singleton signature must contain p and avoid n. The decoder retains only the maximal n associated with each p, which impose the strongest of these requirements. Every omitted neighborhood gives 162 such obligations.

To enumerate admissible triples, choose one obligation and assign any signature that distinguishes it to the first slot. Pick an obligation that remains uncovered and do the same for the second slot. The verifier checks that one slot never covers every obligation. The third signature must contain all remaining positive points and avoid all remaining negative sets, and all possibilities form an explicit subcube. Since the three slots are interchangeable, this enumerates every admissible unordered triple, including repetitions. Only the omitted neighborhood is forbidden. The other six canonical masks may recur among the three further slots.

The verifier next checks all outside-point pairs for each of the six targets. It uses the same raw positive-negative witnesses as the two-extra case, requiring all other canonical neighborhoods that contain the positive point to meet the negative. Imposing this also for the omitted neighborhood restricts the witnesses and is conservative. For target T and outside pair B, if the T output accepted B then for each witness at least one extra must distinguish the positive point from the negative point set. With the first two extras fixed, the possible third signatures again form a subcube. The verifier records targets for which some pair B could thus remain unprotected.

For each omitted neighborhood there are 204,717 admissible unordered triples. For every triple at least five of the six canonical outputs reject every off-target pair. This conclusion applies even if functions with identical singleton signatures differ on larger point sets.

## Counting the gates

Choose five protected targets. If q of these have exactly two charged gates, the five together require at least 15−q charges. Each two-charge target uses three pairs of exterior gates with pairwise signature intersection equal to that target. These pairs are disjoint across targets, so 3q ≤ h(h−1)/2 for h exterior gates. The sixth canonical output also needs a charge. Thus the total is at least 16−q+h. For h=2 through 5 this implies h−q ≥ 2. For h=6, equality q=5 would partition the complete graph on six exterior gates into triangles, impossible by odd vertex degree. For h≥7 use q≤5. In all these cases at least 18 gates are needed. With h≤1 every canonical size-four signature needs three charges: a clean AND of size at least two cannot enlarge the preceding clean signatures, and a clean OR can only combine clean operands. Six canonical targets therefore cost at least 18 gates in this case too. The two-extra proof gives the detailed charge lemma.

## Replay

Compile and run from this folder beside seed-obstructions.

```sh
g++ -std=c++17 -O3 verify.cpp -o verify-six
python3 decode.py | ./verify-six
```

The output columns give the omitted mask, total number of triples, count with zero potentially unsafe targets, and count with one potentially unsafe target.
