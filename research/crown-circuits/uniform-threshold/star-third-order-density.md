# Dense shared incidence doubles the fourth-root coefficient

With C, s, k_U, t_U, h, m, q, e, K and T as in star-third-order.md, one has the stronger conclusion

    liminf [C(n)−2n−√(2n)] / n^(1/4) ≥ 2^(−1/4).

Write p_U for the number of strict probe predecessors. Define D_U=T+2−p_U−k_U. The frozen star flow inequality gives D_U≥0. Indeed the number of shared raw neighbors is at most h−1−p_U−t_U. The number of private raw neighbors is at most 1+f_U+t_U plus all available excess from other shared ORs and shared ANDs, or at most two at low degree. The excess beyond the two units in f_U and the other extra contributions totals at most d=T−h. Adding yields the stated inequality. The degree and comparability sums from star-third-order.md now give

    Σ D_U = F(h)−n+q−(4−e) ≤ 2K.

The star minor implies k_U+t_U≤s+6, so t_U−p_U≤D_U+3. In any topological listing of the shared groups, the number of comparable pairs crossing any prefix cut equals the prefix sum of t_U−p_U. This is at most 2K+3h. Thus the sum of the lengths (position differences) of all comparable pairs is at most h(2K+3h). For any positive integer L there are at most hL pairs of length at most L, and at most h(2K+3h)/L pairs of greater length. Taking L=ceil(√(2K+3h)) bounds the total number of comparable pairs by O(h√(K+h)).

Consider a regular sequence on which (s−√(2n))/n^(1/4) is bounded above. Put t=√(2n). The frozen lower bound gives s=t+O(√t), K=O(t^(3/2)), and d(d+5)/2≤K gives h∼t. Therefore comparable pairs number o(h²). The incomparable missing pairs number q≤K=o(h²). Hence m∼h²/2 and Σ_U k_U=n−e+m∼t². Together with k_U≤s+6 the square-root sum is at least (√2−o(1))t^(3/2). The proven budget Σ_U√(2k_U)≤2K+3h and 2K=s²+7s+14−2n imply liminf (s−t)/√t≥1/√2. The regular-or-delete transfer from star-third-order.md gives the result for all minima, with coefficient 2^(1/4)/√2=2^(−1/4).
