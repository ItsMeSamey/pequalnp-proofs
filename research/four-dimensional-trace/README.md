# A missing rank-four trace beyond pairwise projections

Work in binary six-space, writing vectors as integers with the least significant bit first. The boundary is the low four coordinates, with functional λ extracting bit 3 (mask 8). The eight ordinary columns are 34, 13, 40, 46, 57, 31, 19, 30. For each dual extension d the attainable boundary sums are the intersection of the boundary with the span of the columns on which d vanishes.

| Dual mask | Attainable sums |
|---|---|
| 8 | 0 |
| 24 | 0,1,4,5 |
| 40 | 0,2,4,6 |
| 56 | 0,1,6,7 |

Thus the unique missing output among the eight in ker λ is 3. Every two-dimensional linear projection of the attainable set is surjective.

## Failure of a linear separator

Write π(v)=v shifted right by three bits. A sufficient certificate of absence of p is a linear map T and bits h(v) satisfying T(v)=h(v)π(v) on all ordinary columns, and T(p)=1. Indeed in any representation of p, the selected columns with h=1 would sum to a boundary vector with λ=1. A dual extending λ could not vanish on all these columns.

This certificate fails for the example. Applying T to the zero sum of 13,19,30 forces h(13)=h(19)=h(30). The zero sum of 34,46,31,19 forces h(46)=h(31)=h(19) and h(34)=h(46). Now the sum of 13,40,57,31 is 3. Its two top private output bits must vanish, forcing h(57)=h(31) and h(40)=h(57). All labels agree, giving T(3)=0 as π(3)=0. The accompanying check exhausts all dual extensions, ordinary subsets and candidate labelings.

## Shape of minimal feasible supports

For any rank-four boundary with nonzero λ and attainable nonzero p, choose an inclusion-minimal feasible support X. In the matroid projected modulo the boundary, X is a binary cycle. Let C be the space of cycles supported on X. Summation of the original columns maps C into ker λ because the witnessing dual annihilates X. The map is injective because deleting a nonempty zero-sum subcycle would preserve feasibility. Consequently C has dimension at most three and contains the all-ones vector on X.

Choose a basis for C starting with all-ones. Coordinates with the same column signature in this basis form a class. At dimension one there is a single circuit. At dimension two the two classes support two skew circuits. At dimension three there are either three or four classes, since all signatures start with 1. With three classes the classes are three skew circuits. With four classes the signatures are the four vectors (1,i,j). Their unique dependence sums all four to zero, hence the code on classes is precisely the even-weight code. Every pair of classes is a circuit. Equivalently the restriction consists of four parallel elements expanded by series extensions. These are necessary shapes of a minimal witness and do not by themselves supply a polynomial search algorithm.
