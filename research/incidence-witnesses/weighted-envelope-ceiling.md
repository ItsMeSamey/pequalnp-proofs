# Sharp limit of one explicit scalar envelope

The protected recurrence and repeated residual census give u≤2wN+o(N), G≤3wN+o(N), p=o(N), with w=c−z/N and original surplus allowance cN. Assume total deleted stays below βN for a fixed β<1 so the sparsity and degree bounds are uniform. Write R=n−p−u, J for the number of flattened groups containing a minimal-large source, and γ=(t+4)/(t−2). The physical group bounds imply
```
5R≤12J+18G+O(p),         5R≤(8−t)J+18G+γu+O(p).
```
The incidence lead's refined source bound is J≤R/(t+1)+u/(t−1): group vertices of ordinary degree ≥3 are independent and have total degree at most R. Each chosen source therein needs ≥t+1 ordinary-plus-private tokens. Every remaining chosen source costs at least t−1 private tokens, and the private tokens are distinct. This derivation includes isolated loops.

For integer t=3,…,8 substitute this J bound in the second inequality. For t≥8 put X=5R−18G−O(p), with the same O(p) term in both inequalities: X≤12J and X≤(8−t)J+γu. Multiplying the first by t−8 and the second by 12 yields X≤12u/(t−2). Consequently a strict positive margin in n/N>K_t w earns surplus, where
```
K_t = 2+(t+1)/(6t−3)·[54+2γ+2(8−t)/(t−1)]    (3≤t≤8)
K_t = 2+[54+24/(t−2)]/5                       (t≥8).
```

Take the all-deletion upper envelope with x=z/N, normalized live-site floor a=2−integral t dx, and y=a/(c−x). A prescribed schedule bounds actual deletions even if surplus levels are skipped. At constant t, a−t(c−x) stays constant, and y increases precisely when y>t. The decreasing K_t values obey K₁₃=728/55. Set c*=55/364=2/K₁₃. At the limiting initial value, use t=13 until y reaches K₁₂, then 12 until K₁₁, continuing down through 3. The final live-site floor is
```
(2−13c*) product_{j=3,…,12} (K_j−j)/(K_j−j−1) > 1.05.
```
The exact arithmetic is checked in check-weighted-envelope.py. For each c<c* sufficiently close to c*, shift every switch from K_j to K_j+ε and take ε>0 small. The initial stage is now strictly admissible; each later stage starts with strict positive margin and preserves it. Continuous dependence of the finitely many switch times leaves the final live-site floor above one, so β<1 is available uniformly. Rounding surplus levels costs O(1) total raw deletions. The physical iteration therefore yields liminf s/N≥4+55/364.

For this explicit scalar sufficient-condition system with integer t≥3, c* is the supremum. If c≥c*, initial y≤K₁₃ and no t≤13 passes the strict check. Every admissible t≥14 exceeds this y. Hence on the worst-case all-deletion trajectory y continues decreasing, t cannot fall to 13, and the required deleted fraction is at least 14c>1. This ceiling concerns the displayed n/N>K_t w test and its worst-case deletion accounting, not all physical information about circuits. Allowing t=1,2 through the weaker unspecialized group inequalities cannot change the initial barrier: for t≤2, u=2w, G=3w, R=(K₁₃−2)w and J=R/2 satisfy the elementary group and token upper bounds; in the t=2 case the refined J bound is satisfied as well only after reducing J, e.g. to R/3. Neither small t forces the initial contradiction in this relaxation.
