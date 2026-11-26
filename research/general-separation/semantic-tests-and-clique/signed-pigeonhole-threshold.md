# Sharp signed injection-table levels for binary palettes

There are h holes and N=h+1 pigeons. Level k uses signed integer tables of mass one on each set of at most k pigeons, supported on injections with compatible restrictions. Pigeon-dependent tables are allowed. This level counts entire pigeon labels. The binary 3-CNF in integer-overlap-and-pigeonhole.md has a separate raw-variable budget. Nonnegative local tables alone exist through level h by uniform injections.

## A modular counting obstruction

Write j=N−k. Fix j holes J with 1≤j≤k. Every injection on k pigeons hits J since only k−1 holes lie outside. For S a set of pigeons let u_S be its signed mass that every pigeon lands in J. Inclusion–exclusion on a k-set A gives zero for the mass on which all pigeons avoid J. Terms of order greater than j vanish. Sum over A and use compatibility:
[
0=\binom Nk+\sum_{i=1}^j(-1)^i\binom{N-i}{k-i}\sum_{|S|=i}u_S.
]
If q is a prime power dividing k with prime p and j<q, the constant is one and all remaining coefficients vanish modulo p. These coefficients are binomial(k+j−i,j). The low base-p digit block of size q is j−i for 0≤i≤j. Lucas's theorem gives the claim. Thus even tables over the field of p elements are impossible.

More generally, the level fails if a prime power q lies in [h+2−k,k]. Reduce the tables modulo its prime. Choose a pigeon; its singleton table has total one, so some hole has nonzero mass. Fix this pigeon to that hole and divide the restricted tables by that mass, using the original one-higher tables for all other pigeon sets. This gives compatible normalized tables on one fewer pigeon and hole, down one level. Iterate k−q times. Now j is still h+1−k<q, so the obstruction applies.

Chessboard filling in the companion note proves feasibility for k≤floor((h+1)/2). Taking the least prime above (h+1)/2 and using the prime number theorem gives first infeasible level (1/2+o(1))h.

## A positive construction below the filling threshold

At h=2k−2, k≥2, a unit-mass level-k family exists exactly when k is not a prime power. For prime-power k use the modular obstruction at j=k−1. Otherwise fix 1≤a<k. Split the h colors into sets of sizes 2a−1 and 2(k−a)−1. Chessboard filling gives signed unit-mass tables on the two palettes through respective levels a and k−a. For each way to mark a positions among k ordered slots, put the first top table in marked slots and the second in unmarked slots, taking their product. Sum over the marks. This integer table is supported on injections. Its ordered s-position marginal is independent of the selected positions. A prescribed marking with b marked slots among those s has binomial(k−s,a−b) completions, and its factors are exactly the b- and (s−b)-coordinate marginals in the two palettes. Impossible markings contribute zero. Its restrictions therefore form a compatible family of mass binomial(k,a), assignable to arbitrary pigeon subsets by sorting their IDs.

The intermediate binomial coefficients have gcd one for non-prime-power k. If p divided all of them, (1+X)^k=1+X^k in characteristic p. Write k=p^b m with p not dividing m. The coefficient of X^(p^b) is m modulo p, contradicting the identity unless m=1. Conversely, all intermediate coefficients vanish modulo p for k a power of p. Bézout combines integer families for different a, on the same h colors, to produce mass one.

It follows that for h=2^r≥4 the largest feasible level is exactly h/2 when h/2+1 is a prime power, and exactly h/2+1 otherwise. The middle level k=h/2+1 has h=2k−2. The next level already fails by conditioning to q=h/2 in characteristic two. The lower endpoint always holds by chessboard filling. For h=64, level 33 passes and level 34 fails.

The same positive argument gives palette size 2k−r whenever r≤min_p s_p(k), with s_p(k) the base-p digit sum. Use all positive ordered r-part compositions of k, multiply the r independent tables, and shuffle the slots, giving each composition's multinomial coefficient as mass. For each prime p, group the s_p(k) individual base-p place values into r nonempty parts to get a carry-free composition. Its multinomial coefficient is nonzero modulo p by Lucas's theorem, so the gcd of all masses is one.

This concerns integer local-table proof strength. The formulas have simple counting refutations. For comparison, Ciardo and Živný’s Theorems 2.4–2.6 construct a hollow crystal of width k(k+1)/2 and give a BA hierarchy consequence. The companion filling has sufficient width 2k−1. We do not assert literature-wide priority of the modular incidence argument. [Ciardo and Živný](https://www.cs.ox.ac.uk/Stanislav.Zivny/publications/cz25sicomp-approximate-preprint.pdf) [Björner, Lovász, Vrećica and Živaljević](https://doi.org/10.1112/jlms/49.1.25)
