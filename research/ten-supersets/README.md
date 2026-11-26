# A ten-point boundary extending a noncanonical eight-mask basis needs at least 17 paid point gates

Suppose the singleton signatures of the ten point-side boundary wires contain one of the 202 noncanonical eight-mask bases. The other two signatures are arbitrary and may coincide with each other or with any base signature, even if the corresponding signals behave differently on larger point inputs. At least **17 paid point-only gates** are needed. Thus no 33-gate residual separator with 17 mixed gates uses such a boundary. This proof uses the raw sample decoder, the eight-mask classification, and the elementary charge count below.

## Pair protection from the raw rows

In 175 bases one full target neighborhood is replaced by two proper subsets covering it. In 21 bases a shared singleton is split off from two targets, leaving their three-point remainders. In six more bases this happens to three targets. The checker directly generates these families.

For each full target T designate its output. For a shortened target designate its three-point remainder; in the one-split case designate both covering outputs. Call the target protected when every designated output rejects every pair B of points outside T.

An obligation (p,n) comes from a positive at singleton point p and a negative with point set n whose primitive line coordinates dominate the positive's. For a target T, designated output M, and outside pair B, retain only obligations where B is contained in n and M is the unique base signature containing p and avoiding n. If M accepted B, it would be active on n, so every base signal and every line signal would be dominated on this positive-negative pair. Some extra point wire must distinguish the two rows. Its signature must contain p and avoid n. Hence M can accept B only if the two extra signatures collectively distinguish every retained obligation.

After fixing the first extra, the second must contain the union of all uncovered p and avoid the union of all uncovered n. This specifies a subcube of possible second signatures. The checker takes the union of these subcubes over each target's designated outputs and outside pairs. For fixed p only inclusion-maximal negative sets need to be covered. When the witness set for one test contains the witness set for another, vulnerability on the first implies vulnerability on the second, so the checker retains the inclusion-minimal tests in this union.

The decoder verifies 24 point permutations preserving both the target family and the raw obligations. These partition the 202 bases into 23 orbits. The native checker counts unordered extra-signature pairs with repetition for each representative and weights by its orbit size. This gives the following complete profile, counting a basis with its extra pair. Distinct bases can generate the same final multiset.

| Shortened neighborhoods | Bases | No potentially unsafe target | One | Two | Three |
|---:|---:|---:|---:|---:|---:|
| 1 | 175 | 5,599,834,434 | 270,947,967 | 1,959,189 | 810 |
| 2 | 21 | 687,436,950 | 17,204,220 | 87,918 | 0 |
| 3 | 6 | 196,316,760 | 5,008,248 | 26,160 | 0 |

## Charge counts

A charge for T is a paid gate whose singleton signature lies in T and has size at least two. Different targets' charge classes are disjoint because any two target lines meet in exactly one point. An exterior gate has signature contained in no projective line. Every free primitive is contained in a projective line and meets each target in at most one point.

A first charged OR has size at most two. A first charged AND of size at least three has two dirty parents, each accepting an outside singleton, so it accepts some outside pair, extending a singleton if both outside points coincide. Thus a protected triple needs at least two charges and a protected full target needs at least two. A full target made with a single charge must be an AND of two strict supersets of T, distinct exterior gates whose signatures intersect exactly in T.

At equality for a protected full target, its second charge cannot be OR: an OR would need a pair-rejecting first charge of size at least three, since every other distinct clean input has size at most one. A second charged AND must have a clean parent, or it too accepts an outside pair. The clean parent already has signature T, is the first charged gate, and therefore intersects two strict supersets. The second charge's other parent must also strictly contain T, since the first charge alone is unsafe. The three outside portions of these supersets are pairwise disjoint: a common outside point of two, together with any outside point of the third, would activate the output. Consequently the three distinct exterior gates have all three pairwise signature intersections equal to T. Their three pairs cannot be allocated to any other target.

Write h for the exterior-gate count and q for the number of designated protected full targets costing exactly two charges. Then 3q ≤ h(h−1)/2. If h≤1, every AND clean for T of size at least two has a clean parent: the two dirty parents would otherwise be distinct exterior gates because each contains two points of T and an outside point. A clean AND cannot enlarge a previous clean signature, so a triple needs two charges and a full target three, even without protection. In the following cases take h≥2.

### One split

Append one OR of the two covering outputs. This supplies seven full targets, at least four of which are protected by the table. Choose four protected targets. Among the other three full targets, let r count those using only one charge. The total paid gates after appending is at least

```text
(12−q) + (6−r) + h.
```

Here q≤4 and h−q≥2, by the pair bound for h=2 through 5 and q≤4 for h≥6. A circuit with at most 17 gates after appending must therefore have r=3 and h=q+2. The three one-charge targets require three distinct exterior pairs and the chosen two-charge targets require 3q further pairs. For q=0,1,2,3 the required 3q+3 exceeds the number of pairs on q+2 vertices.

If q=4, all 15 edges on six exterior wires must be used, 12 by four edge-disjoint triangles and three by the single-charge targets. Each vertex has odd degree in the complete graph. Since triangles contribute even degree, the three remaining edges must be a perfect matching. Thus each vertex belongs to exactly two triangles. The six triangle pairs each meet at one distinct vertex: each pair can meet at most once, and the six vertices supply six meetings. For any three triangles labeled A,B,C, the exterior signal shared by A and B contains B, and the one shared by A and C contains C. Their intersection equals A, hence the unique point in B intersect C belongs to A. Applying this to all triples forces the four target lines to pass through one point. The decoder checks that at most three target lines contain any point. This contradiction gives at least 18 gates after appending, hence at least 17 before it.

### Two shortened targets

Use the five full targets and two shortened outputs. Starting from three charges per full target and two per shortened target gives 19. Subtract q, then at most two per unsafe full target or one per unsafe shortened target, and add h. At most two targets are unsafe. Here q≤5 implies h−q≥2: use the pair bound for h=2 through 5; for h=6, q=5 would partition the edges of a complete graph of odd degree into triangles; for h≥7 use q≤5. Thus the total is at least 19+2−4=17.

### Three shortened targets

For four full and three shortened outputs the starting count is 18. Again at most two targets are unsafe and h−q≥2. A total of 16 requires two unsafe full targets, each with just one charge, and h=q+2. Thus q≤2. The two single-charge targets and q two-charge targets use at least 3q+2 distinct exterior pairs, exceeding the number available on q+2 vertices for q=0,1,2. This gives at least 17 gates in the final case.

## Replay

From this folder beside seed-obstructions, run

```sh
g++ -std=c++17 -O3 -march=native verify.cpp -o verify-profile
python3 decode.py | ./verify-profile
```

Each output row gives the number of shortened neighborhoods and the counts for zero through seven potentially unsafe targets. The decoder accepts an optional path to the seed-obstructions directory.
