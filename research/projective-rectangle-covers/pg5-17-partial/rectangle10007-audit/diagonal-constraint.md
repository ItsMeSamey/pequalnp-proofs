# A common row-sum correction for the rectangular cover rank bound

Use the projective nonincidence matrix Z and multiplicity matrix W from finite-field-area.md. For a row with positive excess entries q, put R=25+Σq, Q=25+2Σq+Σq², f=R²/(125Q−4R²). The i-th row v of W Z⁻¹ has its diagonal entry and its row sum both equal to R/25. Indeed Z⁻¹=Zᵀ/5−4J/25, the support of the row lies entirely on its 25 nonincidences, and Z⁻¹1=1/25·1. Its squared norm is (125Q−4R²)/625 by (ZZᵀ)⁻¹. Scale v by (R/25)/||v||². The resulting matrix M has both diagonal and row-sum vector f and squared Frobenius norm L=Σf. Its trace is L. Put D=Σf².

If P is the real orthogonal projection on the column space of M, with rank r, then PM=M. Hence ||P−M||²_F = r−L, using tr(PM)=L. Furthermore Pf=f since M1=f. Thus fᵀ(P−M)1=L−D. Cauchy–Schwarz yields (L−D)² ≤ 31D(r−L) ≤ 31D(17−L). All tests in diagonal_constraint.py use exact rationals. The argument applies to each shore separately.
