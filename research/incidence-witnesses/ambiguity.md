# Bounded ambiguity of separated mixed gates on sparse masks

Let t mixed AND gates have arbitrary Boolean factors A_i(X), B_i(Y) on the point and line masks, respectively, and compute their OR. All pure computations may share gates and use negation. If at most a products accept on every promised input (arbitrary X, |Y|≤q), then

    sum_{j=1}^a binom(t,j) ≥ sum_{j=1}^q binom(N,j).

Each nonempty tested line mask Y has a distinct union S(Y) of incident points. If two masks differ, a line occurring in just one has q+1 points and the other mask covers at most q of them. The corresponding scalar truth-table column is the OR on S(Y). Distinct nonempty-set OR functions are independent over every field: their multilinear polynomials have nonzero top monomials, and one can eliminate inclusion-maximal sets successively. Thus the matrix rank equals the right side. The empty column is zero.

On these inputs inclusion–exclusion for OR truncates at degree a, since no larger family of terms activates simultaneously. Each nonempty subfamily supplies a product of one function on X and one on Y, hence rank at most one. This proves the inequality. For 1≤a≤q/2 replace a by min(a,t) as necessary. The binomial bound sum_{j≤a}binom(t,j)≤(et/a)^a and binom(N,q)≥(N/q)^q imply t≥(a/e)(N/q)^{q/a}. This expression decreases with a in the stated range, giving t≥N²/(2eq)≥Nq/(2e). Thus the target gate count holds even when only mixed gates are counted. The symbol e denotes the natural exponential base.

The line-star construction has N mixed gates and maximum promised ambiguity q (select every point). Small ambiguity is consequently a substantive circuit restriction. The bound uses large line masks and does not follow from four-variable coefficients alone.

## Arbitrary Boolean computation above a sparse low-rank gate cut

Let the output be any Boolean function of t interface signals, with no other inputs to that function. Each signal has point-mask/line-mask matrix rank at most r≥1 on the full promised domain and at most a signals are 1 simultaneously. Expand the aggregator's multilinear polynomial. Terms of degree greater than a vanish. An entrywise product of j signals has rank at most r^j by multiplying separated expansions. Allowing a constant, this gives

    sum_{j=0}^a binom(t,j) r^j ≥ sum_{j=1}^q binom(N,j).

When a≤q/2, bound r^j by r^a to get t≥N²/(2erq)≥Nq/(2er). For a cut consisting of distinct internal gates, r≤18 and a≤q/2 imply Nq≤100s for the whole circuit, with unrestricted depth below and above the cut. The rank and simultaneous-activity hypotheses refer to the full sparse promise. No assertion of such a cut in every circuit is made.
