# Supported row images on one- and two-sum trees

Let the message be the full image of rows supported on allowed real
coordinates and all outgoing ports, under (physical score, raw outgoing
trace). Let p bound the width of this map at any node. Choose real
support inclusion-minimally for that message. The map is injective:
a nonzero kernel word has zero outgoing trace, and a real bit on
which it can be added to delete that position without changing the
message. Hence this physical row space has dimension at most p.

For every child keep its true allowed trace domain. Nonzero child
real rows with zero boundary trace extend by zero to global rows
and are independent across children. Keep the at most p children
having any such row exceptional. At every other proper unary child,
each feasible trace determines exactly one real child word, and each
real word determines its trace since the port alone is no cocircuit.
Thus the trace factors linearly through the assembled physical row
space. For empty trace domain (meaning only zero is allowed) use
empty real support; for the full binary domain use the real part of
a cocircuit through the port. This has a unique extension for either
trace by minimality of the cocircuit. An optional torso support
edge with the lifted real score as its weight models both choices.
A zero-arity interface has empty baseline. A child loop forces its
row trace zero. A coloop allows the free trace with zero real response.
These degenerate proper-real-free responses contribute no discrepancy.

Replacing true child maps with baselines at the same trace domains
keeps the space of compatible tuples isomorphic by preserving the
parent word and exceptional-child choices. All relevant discrepancies
factor through the old physical row space since nondegenerate child
traces are determined by their real words. For degenerate unary ports
the free trace supported on the port has zero real coordinates in both
realizations, and the trace cannot change the physical child score.
Each discrepancy is a linear map from a domain of dimension at most p
to the score space. Keep at most p² additional exceptional children
whose original discrepancies sum to the total. This ensures equality
of full output images on the tuple space, not just agreement of
one target vector. The converse lifts every baseline physically.

For each exceptional relation, add its full zero-trace score subspace
as an independent contribution. Require the parent trace in the
projected domain and add its child score via a fixed linear section.
An allowed fixed slot can be projected out of the row code (transfer
scores by a section and include the kernel image); shorten on slots
required zero. Include outgoing trace bits as score coordinates before
projection. Both projections and shortenings preserve the graphical
cover hypothesis and do not increase its codimension. For arbitrary
linear score maps on a cover, the supported-image oracle tests equality
of the realized image to any prescribed subspace. Account for fixed
subspace additions by enumeration of the unknown remaining image or
by passing to its quotient. Compute the finite tables once in
postorder; at each node choose at most p+p² exceptional children.
This yields XP for fixed score width and bounded LOCAL cover defect,
even if the sum of local defects is unbounded.

Ternary extension under explicit conditions. A coindependent triangle
on the complete child has no nonzero pure row, so boundary traces
again factor through the assembled real words. The attainable domain
Q of row traces lies in the even plane. Use the physical rooted
representatives of regular-markers/README.md. A parallel template
realizes every feasible annihilator by disallowing generators among
its available copies; with missing types use the same monochrome
fundamental-component argument to split every zero-q relation in
the selected columns into its individual line components. Boundary
functionals fix all copies uniquely. In a K4 representative disallow
all spokes for Q=0, the two coordinates of nonzero q for Q=span(q),
or one fixed spoke for Q full. These responses have no zero-trace
kernel. The retained matroid columns plus the fixed contractions span
the original representation in each construction. Thus allowed deleted
columns add no arbitrary row once all retained values are known:
minor rows lift uniquely with contracted values zero. Any support
selection on the physical gadget consequently lifts with its entire
score image. At each exceptional triangle impose Q using coordinate
zeros in the even plane and force the remaining slots allowed.
The unary score-map compression proof then applies verbatim. This
version requires the physical substitutions to preserve an applicable
local exact supported-image oracle, e.g. cographic star slots whose
replacing triangles preserve graph-cycle cover. Arbitrary nonstar
interfaces or degenerate ternary gauges require separate treatment.
