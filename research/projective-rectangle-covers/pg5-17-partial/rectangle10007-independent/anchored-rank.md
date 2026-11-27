# Five mandatory large-rectangle anchors for the 17-cover decision

The official 31-by-31 matrix has 775 zero cells. Let Z indicate those cells. Each line has 6 points and two distinct points have one common incident line, so ZZᵀ=5I+20J. Let W be the ordinary multiplicity matrix of a putative cover with at most 17 rectangles. Then W has rank at most 17, is zero at incidence cells and is a positive integer at every other cell. Write A for its entry sum. Rectangles can be enlarged to maximal zero rectangles without changing the number or losing coverage. We use this only for existence and subsequent shape counts. Maximalization can increase overlap and change a heuristic cost.

## A bound on total multiplicity

The inverse is Z⁻¹=Zᵀ/5−4J/25. For row i let R_i denote its sum in W and Q_i its sum of squared entries. For nonnegative real d_i the matrix diag(d_i) W Z⁻¹ has trace Σd_i R_i/25 and squared Frobenius norm Σd_i²(125Q_i−4R_i²)/625. Its squared trace is at most its rank times its squared Frobenius norm, by projecting the identity onto the column space before taking the Frobenius inner product. Optimizing over d_i, or substituting d_i=R_i/(125Q_i−4R_i²), yields

    Σ R_i²/(125Q_i−4R_i²) ≤ 17.

The denominators are strictly positive squared row norms times 625. The same holds with the two shores interchanged. This argument is due to the companion rank audit.

Let e_i=R_i−25. Its nonnegative excess entries sum to e_i, so Q_i≤25+2e_i+e_i². Therefore the rank cost of row i is at least 1−D(e_i), where

    D(e) = 120e²/(625+50e+121e²).

We must have ΣD(e_i)≥14 on each shore. For integer e≥0 let s=17125/93899 and b=3030/93899. The secant inequality D(e)≤se+b follows from the exact difference

    125(e−2)(e−3)(16577e+2525) / [93899(121e²+50e+625)].

Thus E=A−775≥ceil((14−31b)/s)=72, and A≥847. In particular at least six of the 17 rectangles have area at least 48: the largest area is 60, and a smaller-than-48 maximal rectangle has area at most 45. Missing rectangles may be padded by empty rectangles for these inequalities.

## Why a maximal box has area at least 52

Suppose every maximalized rectangle has area at most 50. The deficit 850−A from the total of seventeen area-50 boxes is at most three. Hence every rectangle has area 50, 49 or 48, using the finite spectrum below. Area 50 rectangles have dimensions 5 by 10 up to transpose. If a row is untouched by all the smaller rectangles, then its excess e is a multiple of five. For these e we have D(e)≤(2/13)e≤se: D(e)/e attains its maximum on positive multiples of five at e=5, by differentiating.

For both shores together each area-49 box touches 14 vertices (shape 7 by 7), and an area-48 box touches at most 19 (shapes 3 by 16, 4 by 12 and 6 by 8, or transposes). Use the shore with fewer incidences of such rectangles. Writing n_49,n_48 for their counts, the rank deficit satisfies

    14 ≤ ΣD(e_i) ≤ s(75−n_49−2n_48) + b(7n_49+9.5n_48).

Since 7b−s>0, 9.5b−2s<0, n_49≤3, the right side is at most 72s+21b=1296630/93899<14. This contradiction proves the claimed area bound.

## Completeness of the five anchors

The centered incidence estimate bounds the smaller side of an empty rectangle by 31√5/(6+√5)<9. For the circulant official table the map (i,j)↦(−j,−i) modulo 31 is an incidence-preserving duality. Apply it to the entire cover when necessary to put the smaller side of the selected box on the left.

The script anchor_orbits.py constructs GF(125) coordinates for the 31 labels and verifies that the complete line set agrees with the official table. Each of its four explicit projective transformations independently preserves that set. The coordinate cycle, transposition, elementary shear, and primitive diagonal scaling generate PGL(3,5) by elementary row reduction. For any point set of at most eight, either it contains a four-point projective frame, or it is contained in one line together with at most one outside point. To see the latter, take a noncollinear triangle: all further points must lie on its three sides in the absence of a frame. Extra points on two different sides would, with the opposite two triangle vertices, form a frame. PGL is transitive on ordered frames and on pairs of a line with an exterior point. Thus enumerating either the complementary at-most-four points around one standard frame or all subsets of one fixed line with one optional exterior point covers every orbit. Mutual maximality is checked by both neighborhood closures.

The script enumerates 695 maximal normalized seeds of area at least 46 and row size at most column size. Applying the four explicitly tested automorphisms partitions their full translates into 13 disjoint orbits comprising 738,575 rectangles. The independent spectrum in ../rectangle10007-audit/spectrum.txt agrees on all narrow-side shape counts. After the area-52 bound just five orbits remain. Each line gives (row size, column size, official row mask, official column mask).

    4 13   29    170913825
    5 11   103   563068940
    6  9   119   546291716
    6 10   1861  195823621
    7  8   1869  187435009

Any solution can be simultaneously relabelled so that one of its rectangles is *exactly* one of these. The other sixteen need not respect a subgroup. The five cases are exhaustive search anchors and give neither a 17-cover nor an impossibility result.

A local restriction also holds. If a point p is covered by exactly two maximal rectangles, neither of which has singleton row side, then their point sides are disjoint apart from p and their union is collinear. A shared exterior point would make multiple non-p lines uncovered. Two distinct exterior points, one from each set, must join on a line through p or else that line is uncovered at p. Fixing such a pair implies that all points of both sets lie on that line. Conversely, two such disjoint-off-p collinear sets cover all 25 required columns at p when extended to their maximal opposite sides. The dual version is identical.
