# A fourth-root lower term for monotone threshold two

Let C(n) denote minimum fan-in-two monotone AND/OR size with unrestricted fanout for the Boolean function accepting precisely inputs of weight at least two. Using the regular-or-delete and shared-group bounds in shared-or-cut.md, we prove

    liminf_{n→∞} [C(n)−2n−√(2n)] / n^(1/4) ≥ 2^(−5/4).

## A star with free opposite occurrences

Take a regular global minimum of size 2n+s, with two distinct OR readers per raw. Its flattened OR groups give a simple raw incidence graph. Fix a shared group U of raw degree k≥2. For each incident edge retain the occurrence opposite U as a free variable. Set one raw slot in U to constant one. Set every other raw slot, including the other U slots, to zero. This computes T₂ᵏ: on every nonempty assignment the original star restriction already made U true, the only changed signal visible outside its private OR tree. The modified empty assignment is dominated by a modified singleton, which rejects.

Let t_U count the other shared groups activated by the all-zero probe overriding U to true. All t_U+1 shared roots, including U, simplify to constant true. When the free bits are zero the U slot is true. Every downstream true wire has a local proof of truth involving only true input pins, so these proofs do not use any free variable.

Exactly 2n−k incoming raw pins are constant. Propagate constants topologically, eliminating every gate with at least one constant pin. For each original gate let c be its number of incoming constant pins, o its number of outgoing constant pins (zero for a nonconstant simplified wire), and l the indicator it is eliminated. Then l+o−c≥0. The only potentially negative case is c=2, when l=1 and the gate is constant with at least one outgoing pin: the output is nonconstant and the minimum original circuit has no dead internal gate. Each constant shared root of fanout f≥2 contributes at least f−1≥1. Summing cancels internal constant pins, giving at least 2n−k+t_U+1 eliminated gates. Consequently C(k)≤s+k−t_U−1.

## Summing the stars

For k≥4 the frozen lower bound gives C(k)≥2k+√(2k)−4. Thus k+t_U+√(2k)≤s+3. For 0≤k≤3 use t_U≤h−1≤s to obtain the uniform bound k+t_U+√(2k)≤s+6. In particular every k≤s+6.

Let h be the number of shared groups, e≤4 the number of raw edges avoiding them, m the number joining two, q the number of missing pairs among incomparable shared groups, T=s+1, K=4+3T+binom(T,2)−n, and F(h)=4+hs−binom(h,2)+3h. Probe activation is a strict partial order and comparable pairs carry no raw edge. Thus Σ_U t_U=binom(h,2)−m−q while Σ_U k_U=n−e+m. Retaining the unused incomparable pairs in the frozen summation gives n+q≤F(h)≤n+K, so q≤K. Summing the uniform star bound yields

    Σ_U √(2k_U) ≤ F(h)−n+3h+(e−4)+q ≤ 2K+3h.

Since k_U≤s+6, the left side is at least √(2/(s+6))·Σ_U k_U ≥ √(2/(s+6))·(n−4). In particular every regular minimum with n>4 satisfies

    s²+10s+17−2n ≥ √2·(n−4)/√(s+6).

Write t=√(2n). Along any regular sequence where (s−t)/√t is bounded above, the frozen bound supplies s≥t−O(1), hence s/t→1. Dividing the explicit inequality by t^(3/2) gives liminf (s−t)/√t ≥ 1/(2√2). Converting √t=2^(1/4)n^(1/4) gives the stated coefficient for regular minima.

Finally along any sequence with bounded normalized excess, follow the three-gate deletion alternative to a regular minimum at m or the four-input base. If r=n−m then s(n)=C(n)−2n≥s(m)+r. The frozen lower bound gives s(m)≥−O(1), so r=O(√n), m/n→1, and the fixed base is impossible for large n. Also √(2n)−√(2m)≤r for m≥4. Therefore s(n)−√(2n)≥s(m)−√(2m), and the regular conclusion transfers without loss of the limiting constant.
