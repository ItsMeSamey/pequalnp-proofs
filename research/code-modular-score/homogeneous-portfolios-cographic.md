## General cographic interface (proposed removal of star hypothesis)

Use canonical K4 spokes u=(I+J)p on the primal side and v(0)=0,
v(q)=q+111 for q nonzero on the dual. Both u and q are in the even
plane. Their dot product is zero for every pair of lanes; in this plane
two nonzero orthogonal vectors are equal. Thus every canonical v(q)
avoids every u, with no choice depending on another lane. Conversely
these local choices realize all true boundary portfolios.

In a cographic torso the q lanes are supported on graph-even edge
sets, whereas p lanes are shores. On nonexceptional slots canonical
real-score contributions via u are linear in p, and via v(q) have the
scalar unsigned Z4 expression separately in each even lane and marker.
In detail add q's linear spoke weights and additionally W=sum of its
three spoke weights when q is nonzero. The latter is the high bit of
the Z4 sum of W (lift each coordinate to 0 or 1) on the q-selected
slot edges, as q has zero or two ones. Sums of such always-even Z4
scores can be combined across slots and lanes. A joint target-bit
equality now has degree at most two in all tagged forest coefficients:
the ordinary terms are affine, and the Z4 high bit is the sum of the
input high bits and the pair products of low bits. Affine endpoint
joins preserve this degree. After fixing all shore colors, the product
of t target equalities has degree at most 2t. Möbius inversion gives a
successful choice using at most 2t tagged fundamental cycles in total.
Thus the same skeleton algorithm works, retaining all Z4 segment sums
in the linkage tests. All virtual p representatives may be independently
normalized to avoid every q on retained slots: if q span is full then
p is zero class, if q span is a line use the scalar normalization,
if it is zero there is no restriction. Raw prescribed exceptional slots
may instead be removed with their endpoint demands, as above.
This uses the general conflict-tree decomposition in the cited scalar
regular-markers proof. Independent audit is being requested.

Fix shore assignments and remove all exceptional edges with prescribed
bits, charging their scores as constants. Pin their endpoint colors.
Restrict to the graph of edges monochromatic in EVERY cut lane. A
successful solution guarantees the residual odd-degree demand in every
even lane has even parity in each component, so a single spanning forest
supports each lane's fixed join. The indicator polynomials use tagged
chords of this common forest. If no nonzero evaluation had weight at
most its degree, evaluating the polynomial on small sets and using
Boolean Möbius inversion would give zero for each monomial coefficient.
With explicit pinned edges removed, no extra pin factor is required.
After choosing the small supports, keep all component color vectors and
pinned endpoint colors unchanged; represent the remaining linear shore
score by at most t original outside vertex/lane contributions. This
does not change any chosen even support or its Z4 score. It preserves
all cross-disjointness and the pinned endpoint requirements.
Enumerate O(t+number of exceptional endpoints) placements and segment
flux masks; the number of exceptional children is at most t, each of
bounded interface size. All score guesses and raw masks have parameter-
bounded ranges; the fixed linkage primitive runs in O_f(N^8+M).
Each conflict-tree node is processed once, giving deterministic XP in
r,s,t and stored witnesses. No counting assertion is made.
