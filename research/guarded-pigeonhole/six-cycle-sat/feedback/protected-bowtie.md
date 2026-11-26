# A protected cap without simultaneous isotropic lines

Use five two-dimensional binary spaces indexed by v,a,b,c,d. All diagonal blocks vanish. Specify each nonzero block by its two outer-product factors, encoding a two-bit column as an integer. Reverse blocks are transposes.

| edge | first factor | second factor |
|---|---:|---:|
| va | 2 | 3 |
| vb | 2 | 3 |
| vc | 3 | 3 |
| vd | 3 | 3 |
| ab | 1 | 2 |
| cd | 1 | 2 |

An isotropic transversal of lines must cover every edge by choosing a line orthogonal to its factor at one endpoint. If v does not cover factor 2, a and b must both cover factor 3. Neither then covers ab. Thus v must cover 2. The same argument on vcd forces v to cover 3, impossible even over field extensions.

Every nonempty union of pairs is singular. To see this, expand its Pfaffian by matchings. Group terms by their multigraph of used blocks. Each component is a cycle. Summing the assignments of the two local coordinates at each vertex of a simple cycle gives the product of the local two-factor determinants. A doubled edge gives the determinant of its rank-one block, hence zero. The only simple cycles are vab and vcd, and each has equal factors at v. Every group therefore vanishes.

A physical realization uses the cyclic word vcdvabvbabadcdc on fifteen positions. Baseline feedback sends j to j+1 modulo 15. Each optional gate rotates the three outgoing successors at its three occurrences in cyclic order. The accompanying checker independently counts cycles for all 32 masks, constructs the shifted paired matrix from the chord endpoints, checks all 31 nonempty principal pair sets, and tests incidence covers. To add protected anchors, take disjoint fixed wires, place one anchor on each and one on the original tour, then join the anchors by a cyclic cap. This inserts the fixed wires into the original tour and preserves the cyclic order of gate occurrences.

The separation between the two arms has cut rank one. The example leaves open a lineability statement restricted to prime torsos. Verification script: check_protected_bowtie.py.
