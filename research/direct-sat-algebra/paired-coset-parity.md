# Polynomial parity on a prescribed half-field coset

Let D be a centered alternating Dickson matrix over K of binary degree 2a, H=2^a−1 and z=λ^H for λ≠0. For the original safe-slope determinant Δ define the coset sum over λ·F_(2^a)^*. Set U_i=e_(i+a)+(√z)^(2^i)e_i for 0≤i<a. Then
[
 \sum_{s\in\lambda\mathbf F_{2^a}^\times}\Delta(s)
   =1+\det D+z\det(U^tDU).
]
Indeed the retained exponents jH for 1≤j≤2^a have upper binary half j−1 and lower half its complement. Their complementary-index principal minors therefore choose e_i if bit i of j−1 is one and e_(i+a) otherwise. For an alternating matrix every determinant is a Pfaffian square. The alternating Pfaffian form evaluated on the a columns U_i is multilinear in those columns, so its square is the sum of all these principal minors with multiplicative coefficient z^(j−1). Odd a gives zero identically for that contribution. The outside factor z reinstates z^j. The endpoints give det D and 1. Checking a coset costs polynomially many bit operations, including the usual polynomial Dickson reconstruction/centering where needed. A singular center yields odd parity on every coset for odd a. For even a, parity can vary.

The same transversal argument fails if one simply selects one location from each block of four when restricting to a quarter-degree subfield. For exponents j(2^b−1), digits in the four b-bit blocks are linked by carries. For b=2 the nonendpoint exponent 15=5·3 gives binary blocks 00,00,11,11; exponent 3 gives 00,00,00,11. The complementary selections can have different sizes. No uniform one-from-four Pfaffian contraction follows. No recursive improvement in the search exponent is asserted.
