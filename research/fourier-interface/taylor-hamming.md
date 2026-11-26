# Regrouping the fixed Boolean substitutions

Write q=J−1 and p_x(X) for the truncated polynomial in the coefficient algebra A[z]/z^J used in the source Boolean-difference step. Its multilinear Boolean reduction has degree at most q. For fixed U and x with U contained in supp(x), sum over E with U⊆E⊆supp(x) and |E|≤q. Set k=q−|U| and h=|supp(x) minus U|. The signed multiplicity is

    b(h,k) = sum_{j=0}^k (−1)^j binom(h,j)
           = sum_{j=0}^k [y^j](1−y)^h.

Thus, for each U of size at most q, impose x_i=1 on U and run the normal group-factorization step with X fixed to the indicator of U. Multiply each group's local summand by (1−y) raised to the number of ones of that group outside U. Carry the computation out in A[z,y]/(z^J,y^{k+1}). On multiplication across groups the markers multiply to (1−y)^h. Apply the linear functional that sums the k+1 marker coefficients to the final grouped answer. Adding this result over U exactly reconstructs the source's Taylor data, including h=0 and k=0. Sending the functional inside sums is valid; it must follow multiplication of group outputs.

The number of fixed substitutions drops from sum_i 2^i binom(n,i) to sum_i binom(n,i) for 0≤i≤min(q,n), with polynomial overhead. For concrete parameters the additional polynomial arithmetic can outweigh the saved substitutions. This improvement does not remove the leading q log(n/q) term in the sparse regime. If the partial-jet variant bounds Boolean degree by a smaller q, the same proof applies with that q.

In the source coefficient algebra A=Q[V]/V^ell, each working polynomial has at most J ell (k+1) coefficients. Stream U and the measurement tuples using the original procedure; at most polynomially many words are live. Marker polynomials have integer coefficients and l1 norm at most 2^h after truncation. Across any product h≤n, so they add at most n bits to the source's l1 norm estimate on common-denominator numerators. The final coefficient-sum functional has output norm bounded by the input l1 norm, and no additional denominator arises. Binomial coefficients of degree j≤min(k,h) can be generated exactly by recurrence. Alternatively, when k>n−|U| only those first n−|U|+1 coefficients are required. All required shifts, coefficient products and additions cost polynomial time per source operation.

The full exponent C_q can also be compared directly: if q=o(n) with q→∞, the ratio of the old and new substitution counts is (1+O(q/n))2^q, by bounding the ratios of consecutive binomial terms. For q≤n/2 the simple upper bound 2^q on this ratio is always valid.
