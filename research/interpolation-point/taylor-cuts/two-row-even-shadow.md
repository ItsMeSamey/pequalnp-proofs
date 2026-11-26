# Two parity conditions on an induced even subgraph

Let G be a finite simple graph. Vertex i has a local parity mark a_i and a syndrome label l_i in GF(2)^2. Seek S with label sum t and with degree in G[S] congruent to a_i for every i in S. The empty set is allowed. The following deterministic subcases and obstruction concern the graph-state normal form of affine NAE.

## All marks zero

The empty set handles t=0. Otherwise a singleton carrying t handles the instance. If no vertex carries t, the two remaining nonzero label types b,c satisfy b+c=t. Write B,C for those classes and Z for the zero-label vertices. Any witness must have odd counts in B and C. If either is empty, reject. A nonadjacent pair from B and C is a witness. From now on all B–C pairs are adjacent.

If a component of G[Z] has neighbors in both B and C, choose a shortest path from any B vertex to any C vertex whose internal vertices are nonempty and all belong to this component, ignoring direct B–C edges. The path has no chords apart from its endpoints' original edge. Any other chord shortcuts to a shorter such path, still with a Z interior. Reinsert the endpoint edge. The resulting induced cycle has precisely one vertex of each required nonzero label and every degree two.

If no Z-component touches both, put B on one shore and C on the other, assigning each Z-component to the only shore it touches or either shore if it touches neither. Exactly the B–C edges cross the cut. Any S with the prescribed syndrome has an odd number |B∩S||C∩S| of crossing edges in G[S]. The sum of the induced degrees on one shore would then be odd, ruling out an all-even witness. These cases are constructive with ordinary component, adjacency and shortest-path tests.

There is no upper bound on the minimum support size in terms of the two syndrome bits. On a cycle of arbitrary length n≥3 give adjacent vertices b,c and all others zero, with target b+c. A witness must include their edge. A proper induced subgraph of a cycle is a forest, and a forest with all degrees even has no edges. The only witness is the entire cycle.

## Arbitrary marks when the unmarked image misses a value

Compute the set E of all syndromes achievable by even induced subgraphs of G using the preceding algorithm four times. If E misses a value y, append a single vertex h, adjacent exactly to vertices with mark one and carrying label y+t. Ask for an even induced subgraph on this augmented graph with syndrome y. Every such witness contains h because E excludes y. Removing h gives exactly the prescribed marks, with syndrome t. Conversely for an original witness S the number of marked vertices in S is even by the handshake identity. Thus h has even degree when added to S and all old degrees become even as well. This gives an exact decision and witness algorithm for arbitrary a under the stated condition on E. The test leaves the general E=GF(2)^2 case open.

Credit for the unmarked cut criterion and the missing-syndrome hub reduction goes to the independent reviewer odd_character_sieve.
