# Simultaneous constant-one substitution for dense mixed gates

Let s count the binary gates of a monotone circuit for the original one-sided projective-plane promise, q≥4, N=q²+q+1. Designate d internal wires each accepting at least αNq² distinct nonincident singleton pairs (0<α≤1). Define

    ε = exp(−αq/2) + q exp(−α²q⁴/(128(q−1)(q+1)²)).

If integers 0≤a≤q/4, 0≤b≤q/2 satisfy sε < (q/(2N))^b exp(−4a), one may simultaneously substitute one for all d wires and propagate constants. The resulting ordinary circuit has at most s−d binary gates, accepts all original flags and rejects every independent mask of at most a points and b lines.

For each designated wire, zero on a random maximal q-line negative implies none of its accepted false pairs occurs, by monotonicity. Applying random-query-supergraph-filter.md to those false pairs gives probability at most ε, whether or not the wire accepts any true flags. By the union bound, the event that any designated wire fails to be one has probability at most sε.

Fix an independent mask (P₀,Y₀) within the two caps. A uniform q-line set contains its b'≤b prescribed lines with probability (q)_{b'}/(N)_{b'} ≥ (q/(2N))^b. Given this inclusion, the remaining draws must avoid all lines through P₀. At most a(q+1) lines are forbidden, disjoint from Y₀. At each draw their fraction is at most x=a(q+1)/(N−q+1)≤1/3. Using log(1−x)≥−2x and 2qx≤4a gives conditional extension probability at least exp(−4a). Thus the probability of extending this mask exceeds the probability of any designated failure. Choose an extension with every designated wire one. After simultaneous substitution the output on this extension is unchanged, by topological induction. Modified monotonicity gives zero on the fixed mask. Flags survive by pointwise increase. Delete each substituted gate once; propagate ones by OR(1,z)=1 and AND(1,z)=z. The empty mask is rejected so no constant-one output remains.

For polynomial s and fixed α>0, some positive c depending only on α permits a=floor(cq) and b=floor(cq/log q) for all sufficiently large plane orders. The reduced circuit is guaranteed on this smaller rectangular testing domain.
