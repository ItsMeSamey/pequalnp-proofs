# Quadratic dependence on fixed OR excess is necessary

For e≥1 take p,q≥2 with p+q=e+3 and p−1,q−1 as equal as possible. Use pq raw labels in a complete rectangular grid. The p row nonempty flags and q column nonempty flags require exactly 2pq−p−q ORs. Return the OR of threshold two on the row flags and threshold two on the column flags. Two distinct grid cells differ in a row or a column, so this computes threshold two. Each local threshold on k flags can use k−1 ANDs and 2k−4 ORs in one AND layer (start with two flags and split raw inputs). Consequently the exhibited circuit has

    n=pq,       O=2n−4+e,       A=p+q−2,
    n−A=1+(p−1)(q−1)=1+floor((e+1)²/4).

Repeated raw splitting increases n and A by one and O by two, preserving the excess and deficit at every larger arity. Therefore the best uniform deficit bound b(e) over single-level circuits satisfies

    1+floor((e+1)²/4) ≤ b(e) ≤ 1+e(e+1)/2.

The upper estimate is proved in fixed-extra-or-single-level.md. The bounds agree for e=1 and determine the quadratic order in e. The grid construction is the classical row/column construction, with its individual AND and OR counts retained here.
