# Homogeneous portfolios on supplied regular decompositions

Fix r primal cycle lanes, s dual cocycle lanes and t joint binary linear
equations. Every primal lane must avoid every dual lane. Within a family,
overlaps are permitted. On a supplied regular sum tree with physical
graphic triangles and cographic K4 slots represented by vertex stars, the
following is a deterministic XP decision and witness algorithm.

In a graphic torso fix successful shore vectors and take one forest
spanning the graph of edges monochromatic in every shore. Expand all r
cycles in its fundamental cycles. Their joint t-bit contribution needs
at most t tagged basis contributions (lane, chord). With boundedly many
exceptional edges remove them, prescribe compatible endpoint color vectors,
and first take one forest join per lane for the induced vertex demands.
Their union still lies in a forest plus t chords. Its vector flows need
not give even scalar degree: absent exceptional endpoints, degree one is
impossible and degree two forces equal incident masks. Keep branches,
endpoints and one anchor per pure cycle. There are O(t + number of pins)
core vertices and segments by summing degree minus two. Preserve each
component's dual color vector. Outside this support and the pinned
endpoints, a basis of t-bit contributions recovers the shore score with
at most t nonzero vertex/lane choices. Enumerate placements, masks on
segments, colors and these extras. Use the scalar oracle's stretching
and clone construction. Enumerate separate edge-score XORs and strict
interior vertex-score XORs for each lane and marker; Z4 endpoint sums
encode each latter XOR. The fixed Liu–Yoo linkage algorithm certifies
one joint subdivision. Check flow balance, pins, component colors and
scores. Cographic torsos exchange families.

For a ternary interface of the complete child, the primal raw trace
classes span P in F2^3/<111>, and the dual traces span Q in the even
plane. The perfect pairing has P perpendicular to Q by binary
orthogonality applied to each cross pair and disjointness on real
positions. If both are nonzero, each is a line; every active lane
uses its family's same nonzero scalar baseline, with raw primal 111
gauges adjusted independently. If only one is active, choose basis
preimages for its trace in the same physical minor, combine them
linearly in each active lane, and set the passive family zero. A
linear minor section adds only contracted primal or deleted dual
coordinates, preserving all cross-disjointness. The existing scalar
real-label factorization therefore applies in each lane, including
missing parallel types. For a unary slot, if any primal lane is
active all dual bits vanish and conversely. Use one fixed circuit
or cocircuit and copy it on the active lanes. Loops and coloops
use the respective zero-cost scalar substitutions in all lanes.

Keep at most t exceptional children by taking a basis of their joint
real-score discrepancies relative to chosen feasible baselines at the
same boundary. Pin their virtual elements and the outgoing slot;
apply physical substitutions at the other slots. The graphic star or
cographic triangle coordinate maps are linear in each lane. Across
lanes disjointness is tested on the physical gadget edges. Parallel
or missing copies use the scalar physical substitutions. Enumerate
the s functionals on bounded-rank basic pieces and keep r column
sums plus the score in the block DP. Compute tables once in postorder,
expand recorded minor lifts or real exceptions, verify all lanes.

Dependencies: /workspace/pnp-research/research/graphic-multiple-markers/README.md
for Liu–Yoo Thm 1.3, /workspace/pnp-research/research/regular-markers/README.md
for pins, missing parallel types, physical lifts and bounded-rank pieces,
and /workspace/scratch/proofsys2026/uniform/cographic-gluing.md for star
slots. A constructive suitable tree or separate general cographic
argument is required to remove the supplied-tree hypothesis. Arbitrary
mixed-root affine demands are outside this statement.

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
