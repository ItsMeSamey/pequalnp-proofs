# Odd-node zero flags for native hypergraph two-colourability

At integer t in the collision grid, let h_t=C′(t)/C′(0). Each row at slot x reads h_t b at a matched column y=x+t and zero otherwise. The subdivision tensor ties its two column occurrences to a Boolean bit. The true scalar sums the product of the old row tensors' multilinear extensions. This follows by evaluating the univariate packet kernel before interpolation.

## Zero flags for a hard 3CNF family under every packing

For a 3-uniform hypergraph take one all-positive clause and one all-negative clause on every edge. This is exactly hypergraph two-colourability, NP-complete even on special linear regular families [Primary hardness result, arXiv:2412.03395](https://arxiv.org/abs/2412.03395). At every odd grid node (of either sign), h_t<0. All row inputs w_i are nonpositive. An all-positive clause has value 1−∏(1−w_i)≤0, with strict inequality if some w_i<0. An all-negative ternary clause has value 1−∏w_i≥1. Equality rows of degree two or three have value ∏(1−w_i)+∏w_i>0, since ∏(1−w_i)>∏|w_i|. Unary variable factors are 1. Consequently all nonzero assignment weights have one sign. If a positive clause has no matched row, every weight vanishes. Otherwise setting all subdivision bits to one gives a nonzero term. Thus the rational odd-node scalar vanishes exactly when a positive clause has no matched row. All odd-node zero flags can be computed by polynomial-time scans of the chosen layout. This criterion applies to every admissible packing, independent of construction order and ties. It does not characterize zero residues modulo a prescribed power of two, higher jets, or even nodes.


The same proof permits any mix of all-positive clauses and clauses having an odd number of negative literals. For the latter, the violation monomial ∏_{neg}w_i ∏_{pos}(1−w_i) is always nonpositive. In particular the ETH connected guard reduction has one exceptional all-positive clause. Its odd-node zero flag is determined by that clause alone.

## Exact jets that can be skipped

Let ν be the number of all-positive clauses at t with no matched port. Each such clause has zero constant term wordwise, so the first ν Taylor coefficients of the true scalar vanish. The whole requested q_t-jet can be skipped if ν≥q_t. More strongly, define g_C=min over its row slots x and real columns y in the same packet of a+1−v₂(t+x−y). There is no zero denominator for such a clause. With α=2L, its row kernel at t+αz factors as
[
W_{xy}(t+αz)=\frac{αh_t z}{t+x-y}\prod_{s'∈S,,s'≠t}(1+αz/(t-s'))/(1+αz/(t+x-y)).
]
All product and inverse factors belong to the 2-local formal series ring. Hence the entire scalar is divisible by 2^(∑g_C) z^ν in that ring. Restoring this known factor permits a lower-precision quotient computation if the clause products are structurally divided before rounding. Dividing already rounded data costs precision. The single-guard family gains at most one Taylor order and a+1 bits, against the native p_t≥8M(a+1). For positive triples, ν≤(P|t|+E)/3 with P packets and E padding holes.

At t=±(L−1) all unmatched denominators t+x−y have the same strict sign. When a fully unmatched clause contributes its first derivative, its sum of reciprocal terms has this sign times sign(h_t), with strict value for the all-ones bit word. Other positive clauses, odd-negative clauses and equalities retain their fixed zeroth-order signs. Thus all nonzero contributions to the coefficient at order ν have one sign, and the all-ones word contributes strictly. The rational vanishing order equals ν at both extreme odd nodes, even in the true summed contraction.
