# Matching module ledger barrier

For the two-stage matching construction ending in a full threshold-five module, let m and w count only used inner edges and incident vertices, and let W=√(2n). The separate gate ledger is 2n+m−w+C5(w). Restricting three threshold-five pins to true gives threshold two on w−3 variables, so C5(w)≥2w−10 for w≥5 by the OR bound. The ledger is at least 2n+m+w−10.

If w≥m^(3/5), this gives the required Ω(W^(3/5)) overhead beyond 2n+W, since distinct labels require n≤binom(m,2). Suppose w<m^(3/5). Write A=Σ binom(deg(z),2)≥2m²/w−m, and D=binom(w,2). The common-neighbor counts c_uv sum to A, and the number J of 4-cycles is (1/2)Σ binom(c_uv,2)≥(A²/D−A)/4. Here m/w^(3/2) grows at least as fast as m^(1/10), so J=Ω(m⁴/w⁴) uniformly for large m.

An endpoint four-set carrying b=0,1,2,3 matchings forces at least max(b−1,0) discarded pairs and accounts for binom(b,2) cycles. The former is at least two thirds the latter. Thus n≤binom(m,2)−(2/3)J, and m−W=(m²−W²)/(m+W)≥Ω(m³/w⁴)≥Ω(m^(3/5)). The ledger exponent 3/10 relative to n is sharp. This argument only concerns the two independent incidence layers terminating in a full prescribed T5 module.
