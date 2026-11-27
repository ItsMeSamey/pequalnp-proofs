# Compiling counts of local gates over affine forms

Suppose a q-input circuit description supplies m Boolean predicate outputs grouped in b baskets. On x the basket values are integer counts of the outputs equal to one. Each predicate is supplied as a function of at most a affine forms on x. A truth table or a polynomial-size subcircuit on the listed forms suffices. Dependencies, repetitions, or shared computations are allowed. The resulting vector selects a polynomial-size system of XORs of products of affine forms on x by a fixed polynomial-time constructor. We count the primary assignments satisfying the selected system.

For each predicate pad to a arguments by ignoring extras. For a truth table f on a bits let W_f(T)=Σ_y f(y)(−1)^{T·y}. These are integers and

    2^a f(y)=Σ_T W_f(T)(−1)^{T·y},
    Σ_T |W_f(T)| ≤ 2^{3a/2}.

The bound follows by Cauchy–Schwarz and Walsh orthogonality since Σ W_f(T)²=2^a Σ_y f(y)²≤2^{2a}. Each character after substituting the supplied affine forms is a sign of one affine form on x. Choose the bit z that is 1 when this sign times sign(W_f(T)) is positive. Replicate z exactly |W_f(T)| times. Thus 2^a f=2Σ z−Σ_T |W_f(T)|. Concatenate the lists within a basket and retain their known scalar corrections. Split each basket's list into chunks of at most q entries. The number of chunks is at most

    h ≤ b + m 2^{3a/2}/q.

Scores of empty baskets are constants. The count-vector constructor sums chunks, restores each original basket count, and calls the original constructor. At an unrealizable auxiliary vector where division fails it may return a false system. All lists and tables are constructed uniformly in polynomial time when a=O(log q) and m is polynomial. More generally use the actual sum of Walsh coefficient magnitudes in place of m 2^{3a/2}.

For instance fix 0<ε<2/9. If m=O(q log q), b≤q^{1/3−ε} and a≤(2/9−ε)log₂ q, then h≤O(q^{1/3−ε}) eventually. The arbitrary-affine-weight theorem applies. With L=log₂(q+2) and A=min(√q,q/h²), its deterministic exact time is 2^{q−Ω(A/(h L⁶))}, including union-of-exception correction. At these parameters the saving in the exponent is a positive power of q for fixed ε. This permits a common affine circuit feeding all the local predicates. For local subcircuits given by binary gates after an explicitly separated affine front end, the affine span of all leaves in a subcircuit can be computed by Gaussian elimination through unions at gates. If that span has rank ≤a, enumerating its basis coordinates gives the required table; the certificate uses syntactic leaf spans and allows arbitrary sharing. [Arbitrary-dependent affine counting theorem](arbitrary-affine-weight-count.md)

**Sharpness for a single scaled sum of affine bits.** For even a≥4, write y=(u,v) with |u|=|v|=a/2. Let f(y) equal the bit u·v except for a toggle at y=0. For the sign g=(−1)^{u·v}, direct summation in v gives W_g(p,r)=2^{a/2}(−1)^{p·r}. Before the toggle the bit function equals (1−g)/2. With the toggle, its nonconstant Walsh coefficients are 1±2^{a/2−1}, and both occur. Their greatest common divisor is one and their magnitudes are Θ(2^{a/2}) as a grows.

Suppose an exact identity wt(list(y))=β+λ f(y) holds for a list of affine bits, with λ a nonzero real number. Every nonconstant character coefficient of a single affine bit has magnitude at most 1/2 and at most one is nonzero. Consequently 2λW_f(T)/2^a is integral for every T≠0. The gcd property forces 2λ/2^a to be a nonzero integer, so |λ|≥2^{a−1}. Comparing all nonconstant normalized coefficient magnitudes shows the list length is at least 2|λ| Σ_{T≠0}|W_f(T)|/2^a=Ω(2^{3a/2}). Thus the worst-case normalization cost in this literal affine encoding is tight up to constants, even allowing an arbitrary real shift and scale.

An arbitrary Boolean decoder of an integer weight is more powerful than this literal identity. For example 2^j repeats of bit j encode the full a-bit argument in one weight of a list of length 2^a−1, after which the entire predicate can be evaluated. Independent baskets and residual equations can also offer other representations. The theorem requires the specified affine supports or a verified low-rank leaf span; unrestricted q log q gate circuits need not meet that premise. [Universal readout and its oracle boundary](adaptive-affine-weight-sat.md)
