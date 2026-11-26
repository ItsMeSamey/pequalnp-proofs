# A sparse restriction that freezes two projective coordinates on each side

Fix two distinct point centers c1,c2 and two distinct line axes d1,d2 in a projective plane of order q. The ith point-coordinate bucket for a line through ci consists of the points of that line other than ci. The jth line-coordinate bucket for a point on dj consists of the lines through that point other than dj. The occupancy of a bucket is the OR of its input bits. The named centers and axes may also be monitored separately.

Assume the scalar circuit passes all incidence tests on masks of at most q lines. Impose the following restriction on its sharing: each internal gate with at least two consumers is determined by the occupancies of these four coordinate families and the individual named center/axis bits. It may use any function of these bits and may have arbitrary fanout. Raw variable wires may have arbitrary fanout. It suffices for the stated determination to hold on the promised domain. Then for every q≥101 the circuit meets the target 100s≥Nq; in fact the asymptotic lower bound is (1/64−o(1))Nq.

Choose a uniformly random incident flag (o,L), by choosing o uniformly and L uniformly among its incident lines. Independently choose P0 as a uniformly random k-subset of L minus o, and T0 as a uniformly random k-subset of the lines through o other than L, with k=floor(q/2). These pads have no incidence. Set their input bits to one. Keep a point free only if it is not a pad or a named center, lies on neither axis, avoids T0, and both its point buckets are hit by P0. Keep a line free only if it is not a pad or named axis, avoids P0, and both of its line buckets are hit by T0. Fix all remaining variables to zero. Every monitored bit is now constant, as are all shared internal gates at the promised tests. Substituting the constants for the shared internal gates leaves a formula of at most s+1 variable leaves, since apart from ordinary input variables every remaining gate has at most one use.

All free points avoid both axes. Among free lines there are at most k occupied buckets on the first axis and a point off that axis is incident to at most one line from each bucket. Thus the free induced graph has maximum point degree ≤k. Every free incident edge is accepted on top of the pads; the pads cannot create any other incidence on a free independent input. For each free edge e=(p,l), select the other free neighbors of l and the other free neighbors of p. These two sets have no incidence by the four-cycle exclusion, and their chosen lines number at most k−1. Together with the k padded lines this gives a legal negative, since 2k−1≤q. Free empty and singleton assignments also reject. The proper-neighborhood rank argument in formula-leaves.md implies the restricted formula has at least as many leaves as there are free edges. Degree-one vertices still require one occurrence by essentiality.

Discard candidate flags (p,l) if p lies on c1c2 or either axis, or if l contains either center or d1∩d2. This discards at most 6(q+1)^2 flags from the N(q+1) incidences. Fix any remaining flag. Require o to avoid l, the two lines c_i p, and the two axes. This has probability at least 1−5(q+1)/N. Given such o require L to avoid p,c1,c2 and both points b_j=l∩d_j. This has probability at least 1−5/(q+1).

Now a_i=L∩(c_i p) are distinct points of L minus o, distinct as well from a0=L∩l. The lines b'_j=o b_j are distinct lines through o other than L, distinct from b'_0=op. If P0 includes a1,a2 and excludes a0 while T0 includes b'_1,b'_2 and excludes b'_0, then both buckets for p and for l are occupied; neither endpoint is selected as a pad, and no pad creates an incidence with either endpoint. Thus the flag survives. Independence of the pad choices yields conditional probability

    h²,  h = k(k−1)(q−k)/(q(q−1)(q−2)).

By expectation some restriction has at least

    [N(q+1)−6(q+1)^2] [1−5(q+1)/N] [1−5/(q+1)] h²

free edges. For q≥101 the three factors relative to N(q+1) are at least 0.94, 0.95 and 0.95, and h≥(q−3)/(8(q−2))>0.12. Hence s+1≥0.012N(q+1), which implies the stated 100s≥Nq. This covers true circuits, including an arbitrary shared internal network operating on those bucket bits. It makes no assertion that the shared gates of a general circuit have that property.

## Growing numbers of coordinate families

More generally let a≥1 distinct point centers and b≥1 distinct line axes be supplied and set m=max(a,b). Assume a+b=o(q) along the family. Then the same model satisfies

    s+1 = Ω(Nq/((m+1)(b+1))).

In particular any o(sqrt(q)) families of each type still require superlinear size, irrespective of the number of shared internal gates or their fanout.

Discard target flags whose line contains any center or whose point lies on any axis. This loses at most (a+b)(q+1)^2 flags. For a remaining flag (p,l), demand that o lie on none of l, the a joins c_i p, or the b axes. Demand that L pass through none of p, the a centers, or the b points l∩d_j. These two independent counting steps give a conditional generic-background probability at least (1−(a+b+1)(q+1)/N)(1−(a+b+1)/(q+1)), uniformly tending to one. The point representatives L∩(c_i p) may now coincide with each other; a coincidence reduces the number of requirements. None equals the forbidden point L∩l or o. The line representatives o(l∩d_j) may likewise coincide but do not equal the forbidden op or L.

For the padding select all q candidate points on L minus o except hP=floor(q/[2(m+1)]) uniformly chosen holes. Select all q candidate lines through o excluding L except hT=floor(q/[2(b+1)]) uniformly chosen holes. The forbidden point is a hole with probability hP/q. Conditional on this, the probability that any one of the at most a required representatives is also a hole is at most a(hP−1)/(q−1)≤1/2. Thus the desired point-side event has probability at least hP/(2q). Independently the line-side event has probability at least hT/(2q). For sufficiently large q these are respectively at least 1/[8(m+1)] and 1/[8(b+1)].

Remove the entire background line L from the free point set in addition to the ordinary restrictions; this does not affect a generic target flag. Every remaining free point lies on |P0| distinct lines joining it to the padded points, all forbidden as free lines, so its residual free degree is at most q+1−|P0|. Because hP≤hT we have |P0|≥|T0|. A proper-neighborhood KW negative therefore uses at most |T0|+q−|P0|≤q lines. This degree bound avoids the extra cost of thinning line-coordinate buckets. The expected surviving edge count now proves the assertion.
