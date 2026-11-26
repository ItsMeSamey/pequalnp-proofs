# Partition-lattice formula and its mass under minor restrictions

For each nonempty row block B let T_B = Σ_j ∏_{i∈B} x_{ij} and c_b = (−1)^{b−1}(b−1)! for b ≥ 1. Then

    per_n = Σ_{π partition of [n]} ∏_{B∈π} c_|B| T_B.

Indeed a column assignment f contributes from exactly the π refining its fiber partition. On any fiber of size t, the sum of products of c_b over partitions equals the sum of permutation signs on t letters: on each block there are (b−1)! cycles, of sign (−1)^{b−1}. The sum is one at t=1 and zero at t≥2 by swapping two letters. Thus precisely bijective assignments have coefficient one.

At all ones the absolute parse mass of this explicit signed expression is Σ_π n^{|π|} ∏_{B∈π} (|B|−1)! = Σ_{σ∈S_n} n^{cycles(σ)}. The cycle enumerator on m letters is z(z+1)⋯(z+m−1): a new letter starts a cycle or can be inserted after one of m−1 existing letters. At z=n, division by n! gives binom(2n−1,n).

Fix any matching minor of dimension k≥1, removing n−k distinct row-column pairs. A block touching two removed rows gives zero because the prescribed columns differ. A block touching both a removed and a retained row gives zero because all retained entries in that removed column vanish. A removed singleton block contributes c_1 times one, hence one. The surviving partitions therefore consist of the removed singleton blocks plus an arbitrary partition on the retained rows. Each retained T_B ranges exactly over retained columns. This proves equality term by term with the dimension-k expression and gives normalized mass binom(2k−1,k), independently of the matching.

Over the prime field F_p, blocks of size b>p have zero coefficient; all sizes 1≤b≤p have nonzero coefficients. The argument establishing the polynomial identity remains valid. For the direct expression lifting each block coefficient to its least nonnegative residue, the normalized absolute parse mass on any k-dimensional minor is

    (1/k!) Σ_{π partition of [k]} k^{|π|} ∏_{B∈π} |lift(c_|B| mod p)|.

This is a mass assigned to the lifted expression, whose polynomial agrees with the permanent modulo p. Other lift conventions can change the mass. With the stated lift the singleton partition contributes exactly k^k/k!, so deletion of all larger blocks cannot bring the mass below this lower bound.
