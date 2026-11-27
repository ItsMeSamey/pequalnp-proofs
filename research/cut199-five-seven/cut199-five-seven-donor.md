# Normal form for cut 199 with five left ports, seven right ports and twelve mixed gates

Incidence gives one doubly used mixed or boundary producer. Cut its two outgoing edges. Its defining cone is a read-once formula and its exterior is a read-once formula on untouched ports and two copies of the donor. A boundary donor has one leaf in its defining cone. Physical port names stay distinct throughout this argument.

## All five-port left encoders

The private-probe chain in one-edge-cut-obstruction.md forces the four literals 0,1,2,6 and a zero spare on the 7-absent face. The singleton 7 supplies precisely the spare, so the spare equals raw 7. Raw 6's marker equals 6 globally. Indeed, on the maximum 6-absent input all four other markers are already one; the 6-marker must be zero because the full left input accepts at empty right and this input rejects. Monotonicity fixes that marker on the whole cube.

For each early vertex i the remaining marker equals xi OR (x7 AND gi), with gi monotone on the other three raw coordinates among 0,1,2,6. No gi can be one at zero. These 19 choices capture all upper-face functions by absorbing xi. The first checker enumerates all 19 cubed triples, allowing every possible producer cost and sharing. It requires that any directed left-cofactor distinction have some directed boundary-bit distinction. Exactly 504 ordered banks pass.

## What a donor can contain

Fix early inputs all high, freezing their three markers. Empty right gives AND of the two remaining left variables 6 and 7, while singleton 3 gives OR. If the donor contains neither, their exterior LCA cannot change operation when both variables are essential. If it contains both, the exterior must transmit the donor, and their inner LCA cannot change either. Thus its left subset contains exactly one anchor.

For each subset of left port indices and each raw right assignment Y, group raw left inputs by their exterior left code. If the target varies on a group, fixing this code and Y makes the exterior a nonconstant monotone unary function of the donor. It must be the identity. Record all resulting positive and negative constraints on the inner left code and Y. The donor is monotone on these formal inputs, even if a combination is physically absent. Close positives upward and negatives downward. An intersection excludes the subset.

If the four corners on two inner left inputs force AND at one setting and OR at another, exclude the subset as well. In the inner read-once tree each such leaf occurs once. Holding the other inner inputs constant can reduce their LCA to a unary or a constant, but whenever both leaves are essential their LCA retains its original operation. This check permits different Y for the two settings and tests only squares all of whose corners have forced values.

Across all 504 banks the only surviving donor-left subsets are the singleton raw port 6 and the singleton raw port 7. This computation imposes no bound on the number or cost of right ports within the donor.

## Guard extraction

With only one left leaf a mixed donor cone is a comb; every sibling on its anchor-to-root path must be a single pure right port. At empty right the high early background with the opposite anchor high forces the donor to transmit the anchor. An AND on that path would kill it. Consequently the donor is the OR of its anchor and all its right ports. The boundary-donor case has no right ports.

Each donor-side right port implies the induced right edge predicate. For any right independent set Y, adjoining vertex 3 leaves it independent. At that assignment the graph changes from zero to one between empty left and the anchor singleton. All exterior left inputs agree on those two low backgrounds. Thus the donor transmits the anchor and every OR guard is zero. Monotonicity gives zero at the original Y.

Extract all these guards to an OR chain at the output and replace both donor occurrences by the raw anchor. On a zero-guard assignment the expression is unchanged; on any positive-guard assignment the target is already true regardless of the left input. This constructs an exact read-once expression with one repeated anchor and each right boundary occurrence used just once. It does not rely on downstream gates retaining their syntactic mixed status.

## Projected costs

There must be two hits on right singleton 3 in a size-at-most-21 circuit. One hit would leave the opposite anchor and the single varying right port each singly used on the majority slice, contradicting their changing LCA. The response count of nine on 3-high, 6=7=0 requires four varying bits, so there are at most three hits. Three hits give four varying right leaves in a read-once tree on that face; the established four-port read-once cost is at least nine, and pinning removes at least two of the three hit producers. This exceeds the full right budget of nine.

With two hits, setting 3 high and both anchors low leaves exactly the three raw left literals 0,1,2 and at most five varying right occurrences in a read-once expression. Every nonraw hit producer vanishes upon pinning. The existing seven-gate projected exclusion in cut199-m12-two-hit-seven-right.md applies to these very leaf conditions. Therefore the right face costs at least eight, at least nine full right gates are required, and a total of 21 permits no paid left gate.

Equality forces the two hits to be raw 3 and a terminal OR of raw 3 with an already available signal H from the other five right vertices. A physical duplicate of raw 3 is also permitted, giving H identically zero on the lower face. No other producer may read raw 3 or its terminal hit; it would fold as well. All other right ports are independent of raw 3. The eight-gate face with five varying right occurrences remains unresolved here. If a pair of those occurrences combines to a pure right subtree, the resulting four varying signals cost at most nine, so the existing strict lower cost of nine for four signals does not eliminate that boundary case at equality.

## Replay

Run `python cut199_all_five_left.py` followed by `python cut199_all_five_modules.py`. The last output must report `Counter({(8, 16): 504})`. The optional exact fixed-portfolio checker test `node replay_cut199_onefork_control.cjs` reconstructs the known 22-gate positive control and verifies every assignment.
