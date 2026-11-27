# Excluding area 850 by repeated binary row classes

Use the notation, real row filter and finite-field restriction B from finite-field-area.md. Suppose total excess is 75. The following cuts are necessary even with split defect rows or shared defect columns.

## Binary rows

Let r be the number of rows with an odd defect, d=r−14 the upper bound on rank B over GF(2), and p the number of these rows having precisely one odd defect. Call the latter rows pure for this argument. Their restricted row is the indicator of nonincidence with their defect line, flipped at the row's own coordinate. Every pure row has a zero at its own coordinate and at most seven zeros overall (the line has only six incident points). It is nonzero since r≥14.

Group pure rows by their full row vector in B. Every class has size at most three, using the four-row contradiction of finite-field-area.md. Let a,b,c count classes of sizes one, two, three, respectively, so p=a+2b+3c. Write t=b+c. For every repeated class C its common vector v_C has zeros at C. Its defect lines are distinct: fixing the same line would still leave distinct elementary diagonal vectors. For a class of size two these two lines meet at a unique point, so at most one coordinate outside C can also be zero. For a class of size three their lines are the three sides of the triangle on their points: each is incident with the other two but not its own. Hence they have no common point. In either case the zero set Z_C has size at most three and contains C.

The binary indicators of Z_C, for the t repeated classes, are linearly independent. Indeed, for any nonempty subfamily of t' repeated classes their disjoint class-coordinate sets furnish at least 2t' selected positions. At most t' further positions counted with multiplicity can come from outside the respective classes, too few to cancel them all. Because v_C=1+1_{Z_C}, one always has t≤d+1. If 3t<r the union of the Z_C omits a coordinate, and the v_C themselves are independent: an odd sum is one at that coordinate and a nonempty even sum is nonzero by independence of the zero sets. Thus in this case t≤d. Also a+t≤2^d−1, and counting ones in all the vectors of a dimension-at-most-d row space yields

    a(r−7)+t(r−3) ≤ 2^(d−1)r

for d≥1. For d=0 there cannot be a pure row.

There is a further constraint when 0<3t<r. Restrict all rows to the complement U of the repeated zero sets. All t independent repeated rows now restrict to the single all-ones vector, so the restricted row space has dimension at most d−t+1. Group the pure row indices lying in U by their vectors **restricted to U**. No such vector is all ones because it has a diagonal zero. If r−3t>7 it cannot be all zero either. There are at most three indices per restricted class: four equal vectors restrict to zero in their own four columns, again forcing two distinct defect lines to contain two common points (duplicate lines would have different diagonal columns). Counting also the at most 3t indices outside U gives

    p ≤ 3t + 3 (2^(d−t+1) −1 −1_{r−3t>7}).

## Ternary rows

Keep the square-rank test in finite-field-area.md. If there is at least one active row with precisely one nonzero mod-3 defect equal to one, its B entries are all nonzero, including the diagonal 1+1=2. Its entrywise square is the all-ones vector. Each of the m distinguished residue-two rows has entrywise square equal to ones except for its own coordinate. Therefore the squared matrix has rank at least m+1: subtract the all-ones row and take its coordinate together with the m distinct distinguished coordinates. Consequently m+1≤(r₃−14)(r₃−13)/2 in this case.

## Reproduction and final contradiction

Run python repeated_classes.py 75. The exact secant gap leaves 4,894 candidate multisets of integer row partitions. Searching a,b,c for the necessary binary inequalities leaves 1,381. The ternary active-count, projective-direction, original square and extra all-ones row checks reduce that count to 233, 47, 4 and 2. The survivors are both pure-only in the stronger integer sense: the nonzero raw excess rows contain a single positive entry. Their counts by entry weight are either {1:5, 2:12, 3:12, 5:2} or {1:6, 2:9, 3:13, 4:3}. Apply the same tests to the transpose. Thus every row and column has at most one defect cell, now as a conclusion rather than an assumption.

A pair of rectangles can therefore meet in at most one cell. A defect of value x is met by x+1 rectangle slots, consuming binom(x+1,2) distinct slot pairs. Summing over the two candidate histograms gives 143 or 141 pairs; at most binom(17,2)=136 are available. This excludes excess 75. Together with the earlier cuts any 17-cover needs area at least 851. At excess 76 the same row filters retain 75 profiles, so this reasoning does not exclude that value or decide whether a 17-cover exists.
