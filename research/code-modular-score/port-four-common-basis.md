# Deterministic common-basis filters for four binary roots

Let A be any binary ordinary column matrix of rank r and let B inject a
four-dimensional named vector space into im A. For an ordinary
independent set F of size r-2 whose root images have rank two, let P be
the two-dimensional image of the component-row restrictions on the names,
i.e. the orthogonal complement of ker(π_span(F) B). Fix a target U for P.
Every achievable U occurs at this size: start from an independent basis
of the witnessed physical span. Two virtual columns spanning a complement
to the named K=U-perp stay independent over it. Extend the forest to
an ordinary basis in the quotient by those two virtuals; its enlarged
span still contains B(K) and excludes all nonzero complement combinations.

For every plane L with L intersect U=0 take two independent linear
functionals defining L as a kernel. Form M_L on the ordinary columns by
quotienting their vectors by the B-images of these two functionals
(identify named coordinates with the dual using the standard pairing).
A set of size r-2 is independent in M_L exactly when it is ordinary
independent and both virtuals survive independently in its quotient.
Such an F has root row-image P of dimension two; its two virtuals
survive exactly when P intersect L=0. For every pair of the 16 planes
L disjoint from U run deterministic linear matroid intersection for a
size-r-2 common independent set and verify its actual plane by elimination.
The two tests always refer to THE SAME ordinary set.

For connected graphic A at size n-3 the three component charges sum to
zero. All three are nonzero after projecting modulo L precisely when
the two projected row generators are independent. Hence each filter is
the fixed-cardinality layer of a Gamma-graphic delta-matroid of Kim,
Lee and Oum. Four complement planes arising from the other four lines
in an F4-spread with U pick out U exactly as a four-way intersection.
Their single-matroid weighted optimization theorem does not compute
that intersection.

A competing plane P masks a pair of filters when it is disjoint from
both. Exhaustive finite verification by port-four-common-basis-check.py
shows that at least six distinct competing planes are needed to mask
every pair. The elementary independent check of every five-plane choice
covers all binomial(34,5)=278256 possibilities. Sharpness follows by
taking all six other planes through a fixed point of U. With at most
six attained planes in total, if U occurs there is some filter pair
whose every maximum witness induces U. Absence of a verified witness
gives a NO under that promise; with no such promise a missing filtered
witness alone is inconclusive. Any infeasible filter pair is an
unconditional NO certificate. This derandomizes the earlier small
spectrum result obtained from forest polynomials and generalizes the
small-spectrum case to arbitrary binary ordinary matrices.
