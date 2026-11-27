# Deterministic lifting by pairwise collision bounds

For fixed ε>0, q=p² with p prime, q^(1/2+ε)≤h≤q, there is a deterministic scalar monotone circuit of size O_ε(Nh²/√q) for arbitrary points and at most h active lines in PG(2,q).

Choose a power of two r comparable to C_ε h/p. Encode N line labels as distinct polynomials f_l over F_r of degree at most d=ceil(log_r N)−1. Since r≥q^ε, d≤D_ε for a fixed constant. Choose r≥(D_ε+1)h/p, so rp>d(h−1) and r>d. For each (z,u)∈F_r² instantiate the cap-p decoder from subfield-one-sided-upper.md using only lines with f_l(z)=u. Write H[z,u] for its output with the full original point payload. Output the OR over l of Y_l AND the conjunction of H[z,f_l(z)] over all z.

A selected incident l makes all its bins accept, even when over cap, by monotonicity and singleton flag correctness. On an independent input each active l collides with each other active line in at most d evaluations by the root bound for nonzero polynomials. Thus among its r bins the total number of other active queries is ≤d(h−1)<rp. At least one bin contains at most p−1 other active queries, so its exact cap-p decoder rejects. Inactive labels cannot fire. This check does not require any single evaluation to balance all bins.

There are r² cap-p circuits of O(Np) gates and O(Nr) binary collection/selection gates. The construction is deterministic because all evaluations specify fixed wiring. Together with the earlier balanced lift up to q^(5/8), taking ε=1/8 for the larger caps gives o(Nq) for every h=o(q^(3/4)). The original cap h=q lies outside this sub-Nq conclusion.
