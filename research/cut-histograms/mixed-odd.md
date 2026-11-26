# Two distinct odd primes and a compressed SAT reduction

Fix m with h≥2 distinct odd prime divisors p₁,…,p_h. From a 3-CNF F on n variables with L clauses construct an explicit binary linear code whose number of codewords of weight **one modulo m** equals the number of satisfying assignments. The deterministic construction time and output length are

    poly(n+L) · 2^{O_m((L+1)^{1/h} log(L+2))}.

This subexponential-size reduction gives no polynomial reduction or NP-hardness claim. A polynomial-time bin-membership algorithm at this m would solve 3SAT in the stated time. Polynomial-time decision for every fixed m would give a 2^{O_ε(n^ε)} deterministic 3SAT algorithm for every ε>0: deduplicate clauses so L=O(n³), and use h>3/ε. No ETH assumption enters.

The low-degree divisibility construction is the composite-modulus OR construction of Barrington, Beigel and Rudich applied to the clause-violation bits. The code reduction additionally expands parity characters, fixes the target to bin one and preserves assignment multiplicities. [Barrington, Beigel and Rudich](https://www.cis.temple.edu/~beigel/papers/bbr-mods-cc.html)

## Construction

Let a_i be the least p_i-power strictly above (L+1)^{1/h}. Their product exceeds L and a_i≤p_i(L+1)^{1/h}. For message x let K count unsatisfied clauses. The indicator f_i of a_i dividing K has degree at most a_i−1 over F_{p_i} in the clause-violation bits. It is the coefficient of z^{a_i−1} in (1+z)^{a_i−1}Π_C(1+z[clause C violated]), by the base-p digit identity in README.md. Each clause violation uses at most three input bits and has at most eight Walsh terms. Truncated multiplication and collection of equal frequencies computes the indicator list in (O(L+1))^{O(a_i)} field operations, up to polynomial factors. All divisibilities hold exactly when K=0.

Introduce a new message bit b, and multiply each indicator by b. All resulting functions vanish at the all-zero message. For p_i^α exactly dividing m, lift the coefficients arbitrarily to Z/p_i^α and raise the lifted Walsh function to the fixed power φ(p_i^α). This produces the exact zero/one indicator in the ring: any multiple of p_i is annihilated since φ(p_i^α)≥α, and every unit becomes one. The fixed exponent increases the list size by at most a constant power. For any 2-primary component use b directly. Convert the odd-component lists to weighted sums of binary parities using χ_a=1−2⟨a,(b,x)⟩. The accumulated constant is the value at the zero message and vanishes. The even-component function b is already one parity.

Combine coefficient lists by coordinatewise CRT, with absent weights zero. For each resulting coefficient w include its least nonnegative representative number of copies of the relevant parity column. Add m copies of each individual input bit, including b, so the code map is injective while preserving the residue. Weight one occurs precisely if b=1 and all divisibilities on K hold, equivalently b=1 and F(x) holds. This proves parsimony, including unused variables.

## An obstruction to polynomial-density arguments

Use r positive unit clauses, with unique satisfying assignment all ones. The resulting code has dimension r+1 and length N≤exp(O_m(r^{1/h}log(r+2))), with exactly one codeword in bin one. Its density 2^{−r−1} is less than N^{−C} for every fixed C and all sufficiently large r. A single subspace meeting the bin in every affine coset must be the entire message space. Thus neither a uniform inverse-polynomial density guarantee nor a polynomial-size subspace meeting every coset holds for two odd prime factors, already at m=15. This does not rule out an adaptive polynomial decision algorithm.

In contrast the finite-difference proof gives density ≥1/(2^d s^{2^d}) for any attainable degree-d Boolean target on the support of an odd-field Walsh predicate of sparsity s. If constant on the support, the support-product uncertainty inequality gives density ≥1/s. Otherwise follow a shift witnessing variation, apply induction to the degree d−1 derivative with sparsity ≤s², and note that each target endpoint can be reached from at most two oriented edges of this fixed shift. This proves the bound.

## A power saving for dense 3SAT from a single mixed modulus

The quantitative sparsification lemma of Calabro, Impagliazzo and Paturi lists at most 2^{εn} bounded-width formulas with n^{O(k)} delay and O((k/ε)^{3k}n) clauses each, preserving the union of satisfying assignments. Take k=3 and ε of order n^{−(h−1)/(h+9)}, rounding to a dyadic rational. Apply the fixed-m code reduction to every output. Assuming polynomial-time membership for this single m, the resulting decision time on arbitrary n-variable 3-CNF is 2^{O_m(n^{10/(h+9)} log n)} times a polynomial in input length: both εn and (n ε^{−9})^{1/h} have the indicated exponent. For h=2 this is 2^{O(n^{10/11}log n)}. The quoted sparsification only promises the union of solutions; this composition is a decision implication. The original formula-to-code reduction itself is parsimonious. [Calabro, Impagliazzo and Paturi, Lemma 1](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/CalabroImpagliazzoPaturi_2010_ipec.pdf)
