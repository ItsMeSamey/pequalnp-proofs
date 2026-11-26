# Four synchronized binary quotient bases for the exact plane

Take ordinary binary columns E spanning V of rank r and independent names u1,u2,u3,u4 with H=span(u3,u4). A realizing ordinary set can be extended using physical independent projections modulo U to a span of dimension r−2 that still intersects U in H. Choose an independent physical basis S of that span. Conversely such an S solves the target.

For each r−2 element set S test the four determinants formed by appending these pairs of named vectors:

1. u1, u2
2. u1, u2+u3
3. u1+u4, u2
4. u1+u3, u2+u4

Their product is one exactly for the witnesses. Indeed the first provides quotient coordinates u1=(1,0),u2=(0,1) modulo S. With u3=(a,b) and u4=(c,d), conditions two and three force b=c=0. Condition four then requires (1+a)(1+d)=1, hence a=d=0. Conversely each determinant equals one for a true witness. Therefore the arbitrary labelled plane query is precisely a common-basis query in four explicitly represented binary matroids, all obtained by quotienting the same ordinary matrix by the designated pairs. A common basis consists of original indices. The coefficientwise product of their four basis-generating polynomials is an exact witness polynomial; a polynomial-time evaluator for this product is not supplied by this reduction.

There is a uniform lower bound for the number of simultaneous nonvanishing probes of this particular form. In coordinate order 12,13,14,23,24,34 let p be the six appended minors for S. It is zero or a nonzero decomposable binary bivector. All thirty-five nonzero vectors satisfying p12 p34+p13 p24+p14 p23=0 are possible; zero is possible as well (e.g. with an independent S meeting U in more than H's dimension, or dependent S). The target value is (1,0,0,0,0,0). Over these 36 inputs, the Boolean monomial evaluation spaces of degrees one through four have dimensions 7,21,35,36. The target's point indicator is outside the cubic span. If zero is excluded the dimensions are 7,21,35,35 and the indicator is cubic. These statements are checked by exact elimination over GF(2). Any determinant formed by appending two linear combinations of the names over a characteristic-two extension is linear in binary p over that extension. If nonzero at the target, some binary linear functional of its value is one there; that binary halfspace lies in its accepting set. Thus three or fewer such protected quotient nonvanishing tests cannot isolate the target on all candidate S. This lower bound permits no side information or changes to the ordinary representation; it does not apply to unrelated reductions or general matroid intersection.

In the displayed four-test solution the corresponding linear forms are p12, p12+p13, p12+p24, p12+p14+p23+p34. Among the 16 decomposable binary forms positive at this target, exactly 584 unordered four-form choices isolate it and none of size at most three do. All four minors involve the same indexed S; separate witnesses or independently evaluated existence predicates do not suffice.
