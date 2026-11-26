# Four binary roots: common-basis and rank-three filters

Use the conventions of port-four-common-basis.md. Ordinary A has rank
r, four independent named columns B lie in im A. Fix target row plane
U, the orthogonal of the desired named kernel. In addition to the
136 pair filters, for every nonzero p outside U run the following test.
Restrict the named coordinate linear combinations to the three-space
p-perp by keeping just the three columns of B times a chosen basis
of p-perp. On restricting the original named row functionals, the new
row plane is the projection π_p(P) under quotient by span p, in these
coordinates. Test exact target π_p(U), a plane in three dimensions.
Equivalently rebase the three surviving virtual columns so their sum
is the desired nonzero named kernel generator. Exact line intersection
exists iff a circuit through all three exists in this represented
binary matroid: an independent minimal ordinary representation of
the generator has no proper subset that lands in their span other
than zero and hence completes the three roots to a circuit; conversely
minimality of that circuit forces exactly the required line.
Use Seymour's polynomial three-terminal algorithm and ordinary
deletion self-reduction.

Take a basis of the resulting ordinary witness span. Choose two
independent completion directions in the three named coordinates
independent modulo that span. Extend the ordinary basis to rank r-2
in the quotient by the two virtual completion columns. The resulting
full original row-image P has dimension exactly two and π_p(P)=π_p(U).
Reverse the original identities only at readout; actual kernel is
verified by elimination. Run identical tests after dualizing the
entire matroid [A B]; its named row-plane is P-perp under corresponding
complementary ordinary deletion/contraction. The four names remain
independent and coindependent in the dual. This supplies 12 primal
and 12 dual filters.

Minimum number of competing planes masking all 160 tests is 10.
port-four-combined-check.py is an exact finite cover search; the
transitive GL(4,2) action permits fixing the target. Thus when U is
attained and has at most nine other attained competitor planes,
one test has witnesses and all its witnesses yield U. On arbitrary
input a verified witness certifies YES, and an empty test certifies
NO. If all tests are nonempty but no returned witness matches, NO
is justified under the at-most-ten-planes promise. Absent the
promise this outcome alone is inconclusive. This avoids independent
witness combinations and uses ordinary matroid intersection only
for two matroids. It does not solve unrestricted four-root recognition.

The binary triple test is described in Seymour, Triples in matroid
circuits, https://doi.org/10.1016/S0195-6698(86)80044-0, with the
constructive binary algorithm given in Section 2 of
https://arxiv.org/abs/2611.20960.
