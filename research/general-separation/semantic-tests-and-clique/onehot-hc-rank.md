# Row-cut rank of directed Hamiltonicity on row-one-hot inputs

Each of the N rows selects one successor in [N], giving a map f from [N] to [N]. The Boolean output is one precisely when f is a single permutation cycle. We allow self-loops and count the singleton permutation as a cycle. For a cut I of k rows, let the communication matrix have one row for each map on I, one column for each map on its complement, and entries equal to the output on the combined map.

**Theorem.** Over every characteristic-zero field, for 0 < k < N the rank is

\[
\sum_{m=1}^{\min(k,N-k)}
\binom{k}{m}\binom{N-k}{m}\binom{2m-2}{m-1}.
\]

The empty and full cuts have rank one. Simultaneous relabeling of vertices shows that only k matters.

**Proof.** A noninjective partial map gives a zero row or column. Group the remaining rows by their image S and columns by the complement of their image. Off-diagonal blocks vanish because the whole map must be bijective. Put m = |I minus S| = |S minus I|. When m = 0 the nonempty proper set I is closed, so this block vanishes.

For m > 0, any partial map on I already containing a directed cycle also gives a zero row. Each remaining partial map I → S consists of m paths from the vertices of I minus S to those of S minus I, traversing the vertices of their intersection. It determines a bijection between the two endpoint sets. Every boundary bijection occurs, since all intersection vertices can be inserted into one of its paths. The complementary side has the reverse endpoint sets and the same description. Gluing gives a single cycle exactly when the composition of the two endpoint bijections is one m-cycle. Removing duplicated rows and columns therefore reduces the block to the long-cycle matrix of the symmetric group on m letters.

After inverting one index, this matrix acts by convolution with the sum of all m-cycles in the group algebra. Over the complex numbers this central element acts on each irreducible representation by a scalar proportional to its character at an m-cycle. By the Murnaghan–Nakayama rule the nonzero characters are exactly the hooks (m−j,1^j), with values (−1)^j. Their dimensions are the binomial coefficients C(m−1,j) by the hook-length formula. Each irreducible occurs in the regular representation with multiplicity equal to its dimension, so the rank is the sum of the squared hook dimensions, C(2m−2,m−1). The minors are integers, so the rank agrees over all characteristic-zero fields. Finally, C(k,m)C(N−k,m) choices of S give this value of m. Summing the disjoint block ranks proves the theorem. The long-cycle communication matrix was studied by Raz and Spieker. [Original paper](https://doi.org/10.1007/BF01192528)

**Half cuts.** For k = floor(N/2), the rank is between 3^N/poly(N) and 3^N. For the upper bound use C(2m−2,m−1) ≤ 4^m. The resulting sum is bounded by the product of the two sums of C(k,m)2^m and C(N−k,m)2^m, which equals 3^N. For the lower bound take m nearest N/3. For each side of size s, the term C(s,m)2^m is within a constant factor of its maximum, as follows from the ratio of consecutive terms, and hence is at least a constant times 3^s/(s+1). Also C(2m−2,m−1) ≥ 4^(m−1)/(2m−1). This gives the claimed lower bound. For other cut sizes the exact sum applies. The half-cut lower estimate does not assert a base of three at all cuts between one third and two thirds.

For an equal split N=2k the sharper order is Θ(3^N/N). Let p_m be the mass at m of a Binomial(k,2/3) variable. Then C(k,m)²4^m=9^k p_m². On the central interval k/2≤m≤5k/6 the factor C(2m−2,m−1)/4^m is Θ(k^(−1/2)) by Stirling. The sum of p_m² in that interval is Θ(k^(−1/2)). Its upper bound follows from max p_m=O(k^(−1/2)) by Stirling; for its lower bound, an interval of O(√k) around the mean has probability at least one half by Chebyshev, so Cauchy–Schwarz applies. Outside the central interval the binomial mass is exponentially small by the binomial tail bound. Multiplication by 9^k proves the claimed order.

**Boolean circuit.** Start a one-hot marker at vertex 1. At each of N steps compute the new position by OR-ing, for each possible destination, the conjunctions of a marked source and its selected edge. Accept precisely when the marker returns to vertex 1 for the first time at step N. A deterministic orbit with that first return visits all N vertices. The construction uses O(N³) fan-in-two Boolean gates and is uniform. Thus the same polynomial-size circuit realizes the exponential ranks on all half cuts.

**Finite check.** The accompanying script generates each cycle once from the cyclic order starting at vertex 1 and performs sparse Gaussian elimination over the rationals on the resulting communication matrices. It checked every cut size through N = 7, including the degenerate cuts. At N = 7 the ranks in increasing cut size are 1, 6, 30, 72, 72, 30, 6, 1. [Checker](./onehot_hc_rank_check.py)
