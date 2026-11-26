# Simple unweighted counting of fixed groves and pair separations

The source reduction permanent-to-grove.md has SHA
8de6e2d5a3518de6af0f605dc0c5729b6fd2be4289fea4fd33dddf4fc0ae6d0f.
Counting spanning three-forests on a simple unweighted graph with
the specified seven-terminal (3,3,1) partition is #P-complete under
polynomial-time Turing reductions. So is counting three-forests
with three specified pair separations. Membership guesses a subset
of physical edges and verifies the forest and terminal requirements.

Evaluate the source tag interpolation on zero-one permanent inputs
and on the identity matrix. Grid coordinates 0,...,2m suffice for
m original edges. Every physical substituted weight has polynomial
integer magnitude by its constant-degree formula. Replace negative
weights w by |w|u, evaluating at u=-1 via ordinary interpolation
from 0,...,n, since every forest uses n-3 edges on n old vertices.
All resulting nonnegative weights remain polynomial. Replace weight
j by j parallel unit edges; multiplicities exactly implement forest
products. Keep all vertices, including isolates and terminals.

Replace each of the m' unit multiedges by a private two-edge path.
The source has no loops. No midpoint can be isolated in a counted
three-forest: for the grove each of its three components contains
a prescribed terminal block; for the pair oracle isolated z, a0
and c0 occupy distinct components. The isolated z remains isolated
through all substitutions. A full path projects to a used old edge;
each inactive old edge's midpoint attaches to either endpoint. The
projection is a spanning old forest satisfying the same conditions.
Each old forest contains exactly n-3 unit edges, so the simple
count equals 2^(m'-(n-3)) times the old count. If m'<n-3 return
zero immediately. All graph sizes, numerical values' bit lengths
and interpolation precision are polynomial. Divide by the identity
normalization and apply the #P-completeness of the zero-one permanent.
This argument claims no hardness for Boolean existence.
