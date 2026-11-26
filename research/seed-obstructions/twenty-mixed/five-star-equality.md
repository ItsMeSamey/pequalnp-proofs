# Ten line wires at twenty mixed gates

Consider eleven point boundary inputs and ten line boundary inputs. A connected 20-gate mixed cone on these 21 wires is a tree. The remaining allocation has ten point gates and three line gates. All seven raw singleton line masks occur. Let E be the union of the three extra line masks, and O the remaining ordinary raw labels. An empty extra can be replaced by zero and suppresses at least its first mixed gate, contrary to the previous lower bound of 20 mixed gates at total cost 33.

## Why the line-only cotree test accepts

If a positive has raw line j and the negative contains its point singleton, the negative cannot activate j. Its line-coordinate difference therefore includes the original singleton j. Any private line coordinate at that positive is this very j. Consequently two line coordinates never get an AND mark at the same positive. The OR-only cotree satisfies all forced line labels for every one of the 8,275 banks. The raw OR-edge counts are in lineonly.log. This necessary-condition test leaves the unconstrained point inputs out.

## Ordinary skeleton and the exceptional bank

Take the raw-line skeleton on O. Its side attachments contain point leaves and exceptional line inputs. With all E inputs zero the root accepts all ordinary incidences and rejects all zero-line point sets of size at most two. At a split, points in the two child neighborhoods and rejection of their union prohibit AND; both OR children inherit their required singleton positives and zero-line pair rejections. At an AND-side attachment, its zero-exception cofactor accepts every singleton on its resident ordinary neighborhoods. This is the ordinary-skeleton argument from the one-repeated-label theorem.

For each ordinary target take its private AND-side cofactors and drop the shared guards. Any minimal shared group has an ordinary companion; an ordinary-active negative extending an exterior pair and meeting that companion forces exterior-pair rejection by the private product. If there is only one ordinary line, there are no shared guards. Let b count all original point leaves in OR-side attachments. These b leaves never occur in an ordinary private product. The o=|O| pair-safe ordinary targets are recovered with at most 11−b−o extra point gates, including the original point leaves used to form constant-simplified side cofactors.

For each exceptional label j use instead the OR of all OR-side cofactors at unit exceptional label j, with its loose inputs set to their actual singleton pattern. At a j-positive, ordinary raw leaves are zero, so an accepting root trace needs one such OR side. If a side accepts an exterior point pair, choose a raw j-active negative containing it and meeting an ordinary resident of its attachment. Every ancestor AND side passes on that negative by monotonicity from the ordinary positive, whose exceptional inputs were all zero. The OR side also passes, a contradiction. Thus all exceptional targets have pair-safe outputs formed from the same b point leaves. In particular for every target point p and exterior point pair x,y at least one of these b singleton masks contains p and omits x,y. The raw witness assertions are replayed in verify.py.

## Counting restrictions

A pure circuit augmented by the ordinary private recovery has at most 21−b−o gates. Its o ordinary pair-safe targets require at least 3o. Equivalently the excess s is 21−4o−b. Negative s is impossible. Also b≤11−o. If three or more exceptional stars are considered in the verified cases, each has an exclusive point, and their three exclusive points need incomparable b-bit codes. Thus b≤2 is impossible. For two exceptional stars b≤1 already follows from s≥0, also impossible. For one exceptional star even b=0 exceeds budget.

The read-once proof only needs singleton masks of the point leaves. The point charge theorem applies to the original monotone functions. A gate is charged to ordinary T when its singleton mask lies inside T and has size at least two. Let h be the number of gates whose signature lies in none of the 13 projective lines, and q the number of ordinary targets receiving only two charges. The pair-safe gate theorem gives 3q≤h(h−1)/2. Other ordinary targets receive at least three disjoint charges. Any exceptional-side input mask of size at least two that is contained in a special star costs a further distinct gate, since such a line is disjoint from the available raw primitive library of nonsingletons. These gates are neither exterior nor ordinary charges. If c counts these input positions and h₀ counts exterior input positions, necessity gives h≥h₀ and h+c≤s+q.

Independently suppose an exceptional-side mask is contained in special target T and covers k of its singleton points. It supplies T's full singleton signature using 4−k more OR gates. Relative to three direct gates this saves k−1 gates. Write d_T for the largest such saving or zero. Appending those special outputs to the ordinary construction yields the seven exact singleton stars, of known complexity 21. Hence Σd_T≤s. This use of the singleton theorem does not assume the completed exceptional outputs reject point pairs.

bank.py checks whether b arbitrary masks satisfy the pair obligations, the charge inequalities and the savings limit. It orders masks by value and permits duplicates or zero. Every outer mask slot in the real tree comes from a distinct original wire, so repeated computed signatures still charge distinct gates. The verifier checks all 24 symmetries on both the 676-row statement's derived samples and the complete projective line family. It separately generates every ten-line family from three unions or intersections, including repeated and empty outputs.

Run python verify.py /path/to/point-pareto with Python-SAT supporting CaDiCaL 1.9.5. The point-pareto folder supplies input.py and the pinned L-meta-18968.json. With up to four exceptional labels the finite domain is empty in all 45 SAT calls. Together with the empty-input simplification this excludes 6,595 of the 8,275 line banks. The 1,680 remaining have five or six exceptional labels.

## Five exceptional labels

For a fixed exceptional j, the OR-side output rejects more than exterior pairs. Let D_v consist of every point set contained in some j-active raw negative that meets ordinary resident v. Any point set in the intersection of the D_v over v in O is rejected by every OR summand: for its own resident v use the corresponding negative, and all ancestor AND guards pass. Each D_v is downward closed. bank_rows.py obtains the maximal members of their intersection by intersecting maximal allowed sets and removing dominated results at each stage. For every j-positive p and each maximal X the point bank must have a mask containing p and disjoint from X.

The stronger calculation excludes every b from three through nine at each of the three geometric representatives with five exceptional labels, removing all 1,575 such line banks. The cumulative exclusions are 8,170 of 8,275. The 105 remaining banks have three disjoint pairs covering six labels, leaving one untouched ordinary line.

### The 105 surviving line banks

Each has three disjoint pair extras and one ordinary raw label O. The final two
projected-mask tests in the verifier exclude b=3 through 9. Hence ten of the
eleven point leaf occurrences are attached on OR sides of the path from O.
At least one AND side is required to reject negatives with O active. Every
such side must retain a point leaf when the six exceptional raw labels are
zero. Thus exactly one AND side exists and it has a single point leaf Q. Its
zero-exceptional cofactor is Q, with singleton signature exactly the four
points of O, and rejects every exterior point pair.

In a monotone formula with just one point leaf, retaining Q at zero exceptional
labels forces the path from Q to consist only of OR nodes. Any remaining
exceptional-only side formula on that path whose value is one at a singleton
exceptional raw label j is incompatible with O-active negatives at j.
More generally, a formula in exceptional labels may vanish on every singleton
without vanishing on every negative. For the purpose of positive incidences and
negative upper bounds we may drop all such OR sides, obtaining the guard Q:
all positive incidences use only zero or one exceptional raw label, and negative
outputs can only decrease. The resulting form is
C_out OR (Q AND (O OR C_in)), where C_out and C_in use disjoint occurrences.
Deleting any such side would in fact save a mixed gate. The released mixed
lower bound therefore excludes it even in the original minimum tree.
