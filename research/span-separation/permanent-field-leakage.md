# Off-permutation support in balanced decompositions

Let n ≥ 2 and B = binom(n,ceil(n/3)). Over any field, suppose the permanent is a sum of s products of two row-set-multilinear polynomials on complementary row sets, each having between n/3 and 2n/3 rows. Let L count pairs (g,m) where m is a nonpermutation monomial with nonzero coefficient in product g. Then

    s (1 + L/n!) ≥ B.

To prove this, write p_g for the fraction of permutation monomials covered by a term. Suppose its first factor uses k rows. For each k-element column set A, let u_A and v_A be the numbers of supported injective assignments on the two sides with column images A and its complement, respectively. Their product is at most k!(n−k)!. The total fraction covered is Σ_A u_A v_A / n!. Bounding each product by sqrt(k!(n−k)! u_A v_A) and applying Cauchy–Schwarz gives

    p_g² ≤ |supp(g)| / (n! binom(n,k)).

Here support sizes multiply for disjoint row sets, and each injective assignment enters one summand. Put x = Σ_g p_g ≥ 1. Summing the preceding inequality and subtracting n! x permutation incidences gives L/n! ≥ B x²/s − x. For s ≤ B this is increasing in x ≥ 1, proving the claim. The case s > B holds directly. Each leaked monomial appears in at least two terms because its output coefficient vanishes. The theorem also applies to outputs whose support is exactly the permutation monomials, regardless of their nonzero coefficients.

## An irredundant cancellation over the binary field

Let E be the product of all n row sums, and let m select column 1 in every row. For i from 1 to n let C_i be the product selecting column 1 in each preceding row, any column except 1 in row i, and arbitrary columns thereafter. The C_i have disjoint nonempty supports whose union is supp(E) minus {m}. Thus E + Σ_i C_i = m over the binary field, while the sum of the support sizes is 2 n^n − 1. No nonempty subcollection sums to zero. A subcollection containing E has coefficient one at m, and a nonempty subcollection omitting E has disjoint nonempty supports. Each term can be factored across the same balanced row partition, and each is computed by a polynomial-size row-set-multilinear circuit. This rules out a polynomial bound on the ratio of collected support mass to output support size for general outputs based only on circuit size, unit coefficients, and irredundancy. A permanent-specific bound remains open in this argument.
