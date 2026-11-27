# Recovering a full weighted packet scalar from signed curve counts

Let K=GF(2^m). Use a fixed number b of field input coordinates and a fixed number of polynomial equations defining an affine set V, optionally on the locus D≠0. Suppose k required bits are H_j(z)=Tr(g_j(z)) where g_j are supplied rational functions regular on V, with a common denominator D and polynomial numerical degrees. The counts below are deterministic and exact. Define d=|H(V)|, which can be much smaller than 2^k even when the Boolean affine span of H(V) has large dimension.

## Obtaining a signed moment

For a bitmask a, compute the integer

    μ(a) = #{(z,y): z∈V, y²+y=Σ_{j:a_j=1}g_j(z)} − |V|.

Over a binary finite field, y↦y²+y is F₂-linear with kernel {0,1} and image the trace-zero hyperplane. Thus μ(a) is the sum of (−1)^(a·H(z)) over V. Clearing D is valid on V. To enforce several equalities, expand the product of their zero indicators as a product of one minus their nonzero indicators. A conjunction of nonzero tests is a single nonzero test for the product. Include D≠0 as another nonzero factor when required. This reduces the signed moment to a constant number of single-polynomial affine counts in at most b+1 field variables, with summed numerical degree. The fixed-arity carry algorithm has polynomial bit cost in the numerical degrees and m. Its auxiliary precision (b+1)m+1 suffices for point counts. The accepted trace bits are correlated; no independence assumption enters.

## Finding the histogram

Maintain the support S and exact counts n_s of all prefixes already learned. Initially use the empty prefix with weight |V|, or stop on an empty V. Choose |S| parity characters of its prefix coordinates forming a basis of Q^S. Starting with the constant-one column, for each prefix bit retain a maximal linearly independent set among the previous columns and their products with that bit's sign column. Induction gives the span of all restricted characters, since multiplication by a fixed sign is linear. After the last bit the restricted characters span all functions on S: the indicator of each prefix is a rational product of linear expressions in its coordinate signs. Record the character masks rather than linear combinations.

Query μ for each basis character multiplied by the next bit's sign. The resulting vector equals the basis-sign matrix times the vector of child-count differences n_(s,0)−n_(s,1). Solve and recover each count by halving its sum or difference with n_s. Entries are integers by their counting interpretation. Drop zero entries. After k stages this learns every trace pattern and its count, making at most 1+kd signed queries excluding optional caching. Fraction-free linear algebra has polynomial bit complexity: sign matrix determinants have O(d log(d+1)) bits by Hadamard, and signed right-hand sides have O(bm+1) bits. All divisions occur over exact integers or rationals before evaluating the source ring. No histogram, trace relations, or low affine rank need be supplied.

## Native canonical tensor family

In a legal supplied packet layout choose 2bm+k distinct packets, one aligned live row/column slot per designated packet. Pin other columns to zero and give all other rows free [1,1] weights. One row tensor of degree 2bm+k accepts the bm complementary bit pairs encoding z∈V and the k bits H(z). It is a compact canonical Boolean tensor whose entries can be tested in polynomial time from the field description. The live columns corresponding to paired bits have unary weights [1,1]; the remaining columns have canonical weights [a_j,b_j]. Choose the size parameter so 2bm+k≤s^(9/10).

Such supplied layouts exist with polynomial padding. For example start with s independent matched edges, take s a sufficiently large power of two, uniformly populate all D_arr=r^(2a) ordered label classes with loads divisible by L, and use the appendix's packing procedure. In the notation of the root, r^a=s^{O(1/131072)} and L=s^{O(1/131072)}. A fixed row label occurs s/r^a times on real edges. Since any packet has at most L slots, this label occurs in at least s/(r^a L) distinct packets, more than the required count after polynomial padding. Select a designated slot in each of the needed packets and merge those equally labelled row vertices. This does not change port counts or the supplied labels and slots. The deterministic greedy labeler on the merged topology may produce a different layout.

The real diagonal kernel w(T)=W_xx(T) is identical in every slot. The other freely summed rows disappear by l₀+l₁=1. The two weights on a remaining row, after summing its column, are a_j+b_j(1−w) and b_j w. In particular, a complement pair contributes w(2−w). Thus at every required working point,

    F(T) = [w(2−w)]^(bm) Σ_s n_s ∏_{j:s_j=0}(a_j+b_j(1−w)) ∏_{j:s_j=1} b_j w.

This formula is a polynomial identity with the prescribed lifts. It needs no inversion of w or division in the source ring. The point counts are computed once; source work thereafter uses polynomially many operations in p_t,e,ℓ,s,k,d for all root evaluations and readout. At W(0)=I the value is the weighted sum over actual trace patterns on V. Choosing [1,V] as each unary table returns the Hamming-weight enumerator when the truncation permits. This is a compact native tensor family; the construction does not recover the required field structure from an arbitrary CNF.

The adjacent trace_histogram.py uses the actual bivariate carry implementation to compute signed moments over GF(4) in a small polynomial example, checks the histogram by explicit field enumeration, and compares the scalar formula against direct unary sums at finite ring residues.
