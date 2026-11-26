# Sharp unrestricted third-order coefficient for monotone threshold two

For minimum unrestricted-fanout binary monotone AND/OR size,

    C(n)=2n+√(2n)+(5/4)2^(9/10)n^(3/10)+o(n^(3/10)).

The upper bound is three-level-matching.md. For the lower bound take regular minima attaining the unrestricted liminf, using regular-or-delete. Retain the notation of unrestricted-matching-exponent.md: t=√(2n), s=C(n)−2n, E=s−t=Θ(h^(3/5)), h∼t, K=(s²+7s+14)/2−n∼hE. The antichain H of shared OR groups of shared raw degree >h/2 has size h−O(E); L denotes the missing pairs within H and q all incomparable missing shared pairs. Write a_sh for the number of shared AND gates. The frozen star flow gives q+h a_sh≤K: every shared AND spends f−1 surplus units per probe but contributes at most f−2. Also a=O(E), all missing shared pairs number O(hE), and the number p of private OR groups is at most 2a+1. Since the private raw neighbor count b_U≤p and Σ(d+3+t_U−b_U)≤K for d=s+1−h, we have d=O(E).

All but O(E) members of H are pure. The total number of nonraw slots over flattened OR groups equals s+h+p−a=2h+O(E), by the k+t'−1 cost of a group with k raw and t' nonraw inputs. At least 2|H|−2a=2h−O(E) of these slots are driven by H, all outside H since an OR-only path between two high groups gives a probe comparison. Only O(E) nonraw slots occur in H.

Use the receiver construction of unrestricted-shared-cover.md: g∼h selected pure high groups, called rows, have two distinct OR receivers, and each row misses o(h) high raw neighbors uniformly. There are O(E) original receiver groups. Remove rows having two private receivers using the one-pin-per-AND bound, then peel vertices of degree below two, still retaining g∼h rows. Each row either has two shared receivers or has one shared S and one private P. A raw AB means a single input whose two groups are A,B.

## Effective columns

Keep the root of a shared receiver as its column. From a private P follow its unique outgoing pin until the first physical shared gate D(P) or the circuit output. All internal gates of this chain have one outgoing pin. Thus every path from a row meets one of its two effective columns before it can affect the output.

Fix an original shared S and pivot F∈H. Restrict to the actual raws FA_i for rows A_i=(S,P_i) with P_i private, and override F and S true. If at least two rows remain this computes threshold two: both overrides were already true on nonempty assignments, and the modified empty is dominated by a rejecting singleton. Each pure A_i now supplies its own bit x_i through its sole visible occurrence in P_i: its input occurrence at F is cut and its outgoing branch to S is cut. Delete the private interiors ending at the overridden roots and bypass the pure copies of the input bits. No nonraw path can enter such a pure source. Keep original fanout≥2 gates as marked boundaries even if their current fanout is smaller, and mark the output. The first boundary of x_i is D(P_i). If its chain hits a forced root first, its bit cannot affect the answer, impossible for a nontrivial star.

A boundary is a monotone formula in incoming earlier boundary signals and fresh bits whose unique path ends there. Each fresh bit occurs once. If the star has at least three bits, two bits x_i,x_j cannot have the same first boundary D. Fix all other bits. All earlier boundary inputs to D are independent of x_i,x_j, and the downstream output is a monotone unary function of D, hence the identity whenever dependence survives. Setting the other bits zero requires dependence x_i∧x_j; setting a third bit true and the rest zero requires x_i∨x_j. The least common ancestor of the two leaves at D has one fixed connective. Whenever both leaves remain essential, the two paths below this ancestor and the path above must transmit their respective Boolean arguments unchanged. Thus the fixed connective would have to realize both AND and OR.

At most one bit leaves its first boundary unchanged on its singleton relative to the forced empty. Otherwise on the pair of two silent bits consider the earliest boundary that changes. None of its previous boundary inputs changed, and at most one of the two fresh bits is assigned there, so it cannot change. The output must change, contradiction. Monotonicity means every nonsilent singleton makes its boundary true. On the actual singleton FA_i the two overrides have no effect. Thus at most one row per (S,F) in stars of size ≥3 is cold, meaning an effective column fails to be true. Count both rows as exceptional in smaller stars. The two-shared rows never have a cold column on an incident singleton.

The total number of exceptional row–pivot pairs is O(hE). Discard o(h) rows so each remaining row A has only o(h) high pivots F with FA missing or cold, uniformly, by averaging since E=o(h). No remaining column is the output, by singleton rejection. There are no loops: a private path ending at its own shared S makes all row influence pass through S, and some different original row B incident to S and common high raw neighbor F then give singleton BF hiding added AF. The original two-core supplies B. There are no parallel effective edges: if distinct A,C have identical column pairs (even in opposite orientations), choose F with AF hot and both AF and CF actual. Adding CF to AF is invisible. Pass to the two-core of this simple effective graph; there are only O(E) possible columns, images of the O(E) original receivers, so g'∼h rows remain.

## Column budget

An effective OR column W has o(h) raw neighbors in H. For an incident retained row A, W is downstream of A and distinct from it. All but o(h) actual singletons AF activate W and F, hiding added raw WF if it existed. In particular W∉H. Nor can W precede B∈H in probe order: if B≠A choose hot AF with actual BF, possible since B has >h/2 shared raw neighbors and h−O(E) are high. The singleton AF would activate B and F and hide BF. The case B=A contradicts acyclicity.

Only o(h) high groups probe W true. Choose an effective edge C=(W,N) and a distinct A incident at N from the two-core. If B probes W true, and AB is hot and CB actual, then adding CB to AB cannot propagate beyond C's already-true effective columns W,N. All but o(h) high B meet the row qualifications. Consequently each effective shared OR column consumes h−o(h) incomparable missing pairs into H, distinct across such columns and outside H×H. The AND columns are shared and number at most a_sh. For z=L/(hE), the total effective vertex count satisfies

    w ≤ (q−L)/(h−o(h))+a_sh ≤ (1−z+o(1))E.

## Four-cycle losses

Two different perfect matchings on the same four effective vertices cannot both be actual hot raws, since adding the second raw cannot change the first's already-true columns. Here hot means both constituent rows are hot on this singleton. There are only L missing and O(hE) cold candidate pairs, so initially #C4=O(hE): on a four-set with b≤3 matchings at most one is simultaneously hot and actual, and binom(b,2)≤3(b−1)/2 for b≥1. With T the sum of codegrees over unordered vertex pairs, Σcodeg²=T+4·#C4. Cauchy–Schwarz gives T=O(w²+w√(hE))=O(h^(7/5)), hence Σdeg²=2T+2g'=O(h^(7/5)).

Only cold raws competing on a multiple-matching four-set need be discarded. If AB was cold on the private path of A, its charge is (S_A,B) where S_A is A's original shared receiver and an effective endpoint of A. Since A and B are disjoint effective edges on that four-set, the second matching requires S_A to neighbor some endpoint V of B in the effective graph. Thus there are at most Σ_V deg(V)² possible relevant charge pairs: choose V, an incident row B, and a neighbor S_A. Each pair was assigned at most two exceptional labels in the original stars. This accounts for o(hE) relevant cold candidates. Therefore the matching loss, the sum of max(0,b−1) over four-sets, is at most L+o(hE).

Apply the nonedge codegree argument of matching-codegree-constant.md. We have g'∼h, w=O(h^(3/5)) and loss O(hE). Adjacent pairs receive o(T) of the wedge mass, and Cauchy–Schwarz on nonadjacent pairs yields at least (4−o(1))h⁴/w⁴ unordered pairs of common neighbors at nonadjacent endpoints. A four-set contributes at most twice its matching loss. Therefore L+o(hE)≥(2−o(1))h⁴/w⁴. It follows that

    (z+o(1))(1−z+o(1))⁴ E⁵ ≥ (2−o(1))h³.

The maximum of z(1−z)⁴ for 0≤z≤1 is (1/5)(4/5)⁴. Thus liminf E/t^(3/5)≥(5/4)2^(3/5). Since t^(3/5)=2^(3/10)n^(3/10), the unrestricted lower coefficient matches the constructive upper coefficient.
