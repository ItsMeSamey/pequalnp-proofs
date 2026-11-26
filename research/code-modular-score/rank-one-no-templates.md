# Rank-one NO certificates

Write C for the input binary cycle space. Budget (a,b) controls the
dimensions lost from C and added to C across the intersection with a
regular reference R.

For an ordered partition, form each factor by shortening on earlier
blocks and projecting away later blocks. Dimensions of these successive
factors sum to the original dimension. The factor of C intersection R
is contained in the intersection of the two factors. Subtracting the
dimension sums proves that both directional discrepancies sum to at
most (a,b). In particular, if a+b+1 such factors are nonregular, select
one seven-element Fano or dual Fano minor from each and prepend its
block's shortening/projection. Any candidate within budget leaves at
least one designated factor unchanged. These a+b+1 fixed tests certify
NO, including when the full host is connected and of unbounded width.

On direct sums the converse holds for every directional split, by
assembling a direct sum of local references. Consequently, for either
one-sided budget of one, the disconnected minor-minimal NOs are exactly
the three unordered pairs of Fano types. Each Fano type admits a unit
repair in each direction by contracting an element and inserting a
loop, or deleting the element and inserting a coloop. The original
Fano types have no loops or coloops, so the preserved-coordinate
costs are exactly one. If only one nonregular summand is present, it
alone decides feasibility. With multiple nonregular summands two Fano
type minors already obstruct.

For a proper binary 2-sum on physical sides E1,E2, let Ui be the
projection onto Ei and Vi the shortening to Ei. The quotients Ui/Vi
are one-dimensional and the original code equates their quotient bits.
The rooted summand has code {(u,phi_i(u)): u in Ui}, where phi_i has
kernel Vi. Consider a strict enlargement by one vector z.

* If both restrictions of z belong to Ui, the enlarged code is the
  direct sum of the Ui. This is regular exactly when both Ui are.
* If z1 is outside U1 and z2 lies in U2, the projection and shortening
  on side 2 remain U2,V2. The enlarged code therefore has connectivity
  one across this cut. The rooted side-2 summand is unchanged and is
  a minor: in the other rooted side retain a circuit through the port,
  delete its complement and contract all but one physical circuit
  element and the virtual port. This yields a parallel proxy. The
  other mixed case is symmetric.
* If both restrictions lie outside Ui, both shortenings remain Vi,
  hence both Vi must be regular.

Thus when both rooted summands are nonregular, a rank-one enlargement
requires that the two projections both be regular, or that the two
shortenings both be regular. The first condition suffices; sufficiency
of the second has not been established. Duality exchanges shortening
and projection and exchanges enlargement and restriction.

There is no claimed unrestricted template bound or classification of
all connected minimal NO instances.
