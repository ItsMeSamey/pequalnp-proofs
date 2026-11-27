# Minimum distance and randomized decoding of affine majorities

Let q=2m+1≥5. An affine majority has the form g(x)=sgn(Σᵢ yᵢ), where yᵢ=εᵢ(−1)^{aᵢ·x}, εᵢ∈{−1,1}, and the q vectors aᵢ form a basis of GF(2)^q. Distance is the fraction of all inputs on which two functions differ. Define

    α = binom(2m,m)/4^m,    β = α/(2m−1),    Δ = α−β.

The minimum distance of this class is exactly Δ/2. Given membership queries to an arbitrary sign function f promised to lie at distance at most Δ/4−η from some affine majority, with supplied η>0, a randomized algorithm returns a signed basis computing that majority at every input. Time and queries are polynomial in q, 1/η and log(1/δ) for failure probability δ. The tolerated corruption is Θ(1/√q) for a fixed relative margin.

## Signed heavy characters

For ordinary majority the coefficient of a size-(2j+1) set equals α(−1)^j binom(m,j)/binom(2m,2j); even levels vanish by sign symmetry. For a direct derivation, take the normalized derivative in one member of the set. It is the indicator that the other 2m coordinates tie. On that central slice, a uniformly chosen 2j-subset has mean sign product equal to the coefficient of z^{2j} in (1+z)^m(1−z)^m divided by binom(2m,2j). Exchangeability gives the same average for any fixed subset. Multiplying by the tie probability α proves the formula. It agrees with [O’Donnell, Theorem 5.19](https://arxiv.org/abs/2105.10386).

The ratio of successive unsigned binomial quotients is (2j+1)/(2m−2j−1), so the unique maximal levels are 1 and q, and every interior coefficient has magnitude at most β. An invertible affine substitution relabels all characters bijectively and multiplies coefficients by the products of the relevant signs. There are exactly q+1 heavy labels, the original basis and its vector sum. Multiplying each corresponding character by its coefficient sign yields the list

    y₁,…,y_q, (−1)^m ∏ᵢ yᵢ.

At every input their product is (−1)^m. A tied list of length 2m+2 would have product (−1)^{m+1}, so there is no tie. Its majority therefore survives deletion of any one entry. Any q of the frequency labels form a basis, since their only nonzero linear dependence uses all q+1. Thus any deletion reconstructs the same function exactly.

## Distance and sharpness

If the heavy supports of g and g′ differ, a label heavy on one side has coefficient difference at least Δ. Every normalized Walsh coefficient difference is at most twice their distance. Equal supports with unequal heavy signs instead give coefficient difference 2α; equal signed supports determine the same function by the deletion argument. Thus the minimum distance is at least Δ/2.

For equality, compare ordinary majority with the one replacing y₁ by −y₁y₂y₃ and preserving the other coordinates. This signed change is invertible. It changes the vote precisely when the remaining 2m coordinates tie and y₂=y₃. On the tie slice the second event has probability (m−1)/(2m−1). Multiplying by α gives Δ/2. Splitting the disagreement points as evenly as possible gives a received word within ceil(2^qΔ/4) flips of both. This is the information-theoretic obstruction to unique decoding, with integer rounding.

## Recovery from membership queries

Under the noise promise, each normalized coefficient shifts by at most 2 dist(f,g). With τ=(α+β)/2, every heavy label of g has magnitude at least τ+2η for f, while every other label has magnitude at most τ−2η. Heavy signs are preserved. Use Goldreich–Levin with cutoff τ/2 to obtain a polynomial-size list containing every label above that cutoff with probability at least 1−δ/2. Independently estimate each listed signed coefficient to additive η with simultaneous failure probability at most δ/2 using uniform random queries, multiplying the answers by the corresponding characters. Threshold the estimates at absolute value τ and use their signs, then discard one returned heavy character. On sampling failure a malformed list may be rejected. On success the preceding argument gives an exact signed basis. [Goldreich and Levin](https://doi.org/10.1145/73007.73010)

This is randomized recovery of the underlying function. Supplied side equations on x can subsequently be combined with its recovered affine weight test. Recovering a corrupted oracle’s exceptional positive witnesses requires additional information: even given the clean majority, a side test restricting to its negative half leaves 2^{q−1} possible sites for one positive flip. An all-negative search on that half requires that many deterministic oracle queries.
