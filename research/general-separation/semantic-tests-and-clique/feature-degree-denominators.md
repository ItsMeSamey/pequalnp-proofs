# Feature degree over prime fields constrains real denominators

Fix a finite Boolean feature matrix A with S columns including the constant-one feature, and a Boolean target f. At prime p let d_p be the least degree of a polynomial over F_p agreeing with f on all realized feature patterns, floored at one. Set d_p=∞ if f is not determined by the features. When d_p is finite one may multilinearize on Boolean features. Define

    L = product over primes p of p^ceil(log_p d_p).

Take L infinite if infinitely many factors exceed one or any degree is infinite. Then L is finite exactly when f is a real linear combination of A. In that event L divides every positive integer H for which Aw=Hf has an integer solution w, and there is such an H≤max(1,S^(S/2)). All statements concern the same proposed dictionary.

Suppose Aw=Hf and write H=q h with q=p^v and p not dividing h. Reduce each w_i modulo pq to a nonnegative integer c_i. On every row the nonnegative T=sum c_i A_i is congruent to q h f modulo pq. The base-p digit in position v of T therefore equals h f modulo p. By the binomial digit identity this digit is the coefficient of z^q in (1+z)^T in F_p[z]. Equivalently it is the coefficient of z^q in

    product_i (1 + A_i ((1+z)^c_i − 1)).

Every nonconstant-in-A_i choice has z-degree at least one, so the desired coefficient is a polynomial of feature degree at most q. Multiplying by h^(-1) recovers f. The digit identity follows by writing the exponent in base p and expanding (1+z)^p=1+z^p. [Lucas](https://www.jstor.org/stable/2369308) Hence d_p≤p^v for every p, proving the claimed divisibility. If f is in the real span, Cramer's rule gives an H within the stated bound. If f is outside, a nonzero integer augmented minor D of order rank_R(A)+1 witnesses failure of linear membership modulo every prime not dividing D, since every same-order minor of A vanishes. As a constant feature is present, d_p>1 for all such p. This proves the converse.

## Sharp examples and a failure of the converse bound

For any nonempty finite collection of distinct primes p choose positive v_p and write q_p=p^v_p. Give its block 2q_p−1 coordinate features. Realized patterns consist of zero and every vector supported on a single block with exactly q_p ones in that block. Let f be zero at zero and one on all other patterns. Adding a constant feature is understood. Coefficient 1/q_p on every feature of that block gives a real expression with common denominator product q_p.

For a selected p restrict to its block of size 2q−1, q=q_p. A degree less than q polynomial computing f would have constant zero and sum to binomial(2q−1,q)=1 modulo p over all q-subsets. Each multilinear monomial on j positions for 0<j<q instead contributes binomial(2q−1−j,q−j)=binomial(2q−1−j,q−1), divisible by p. The bottom indices q−1 have every low digit p−1, while the top misses at least one such digit. This is a contradiction. Together with the upper bound, d_p=q for each selected prime and d_p=1 for the others. Thus L equals the minimal common denominator exactly here. The feature domain is finite and can be made total by mapping unused row indices to the zero pattern.

For an opposite example take the first doubling chain in [the dyadic-window argument](dyadic-span-window.md) with length k and add a zero-feature row labelled zero before adjoining the constant column. It forces the intercept to vanish in every exact real representation. The minimal denominator is 2^k since the chain forces a_k=2^(−k) and all extensions have denominators dividing 2^k. Thus d_p=1 for odd p. Each nonconstant feature pattern has Hamming weight ≤3, so any function on the realized patterns has degree ≤3 over every field: extend its values arbitrarily to all subsets of size at most three and determine monomial coefficients in increasing subset order by subtraction. Higher-order monomials are unnecessary. In particular L≤4 even when 2^k is exponentially large in the number of features. Low degrees can leave large denominators undetected.

For an individualized candidate one can refute real sparsity by forcing the prime-degree product past its determinant ceiling. A lower bound for a class requires this for every list of the claimed size, or another way to exclude that entire class. Neither the finite pattern examples nor this membership criterion establishes such a result for unrestricted signed formulas or shared polynomial-time algorithms.
