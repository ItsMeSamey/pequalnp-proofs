# A two-block moment lower coefficient

For the unrestricted fan-in-two monotone threshold-two size, the liminf of (C(n)−2n−√(2n))/n^(3/10) is at least the algebraic constant c*≈0.89074957018 defined below.

Use the two-core receiver graph of unrestricted-shared-cover.md on a regular subsequence with bounded normalized excess, z→z₀. There are g∼h edges, all incident to a shared vertex cover of size u≤(1−z+o(1))E. The preceding shared-cover proof gives 0<z₀<1 and u=Ω(E): otherwise its inequality L≥(1−o(1))g⁴/[8u²(W−u)²] with W=O(E) contradicts L=O(hE). Pad the private class by isolates to total W=(3+z₀+o(1))E. Both classes now have size Θ(E).

Let A be the adjacency matrix and N the two-column matrix of normalized class indicators. Put Q=NᵀAN and X=NᵀA²N. Since I−NNᵀ is an orthogonal projection, X−Q² is positive semidefinite, so ||X||_F²≥tr(Q⁴). Let Y be A² with diagonal and adjacent-pair entries zeroed. If T is the unordered codegree sum, the total of removed entries is at most 2g+2√(g(T+6L)). By Cauchy on O(E²) pairs and Σcodeg²≤T+6L one has T=O(E²+E√L)=O(h²/E), using E=Θ(h^(3/5)). Thus the removed entries sum to o(h²/E), so each entry of X−NᵀYN is o(h²/E²). Projection does not increase Frobenius norm. The prior nonedge matching argument gives L≥(1−o(1))||Y||_F²/8: the nonedge linear sum is negligible relative to its square sum since the linear sum is Ω(h²/E)≫W². It follows that L≥tr(Q⁴)/8−o(h⁴/E⁴).

Let α be the fraction of shared–shared edges, σ=u/E and π=(W−u)/E. Then Q=(g/E) times a symmetric matrix with diagonal entries 2α/σ,0 and off-diagonal entry (1−α)/√(σπ). For fixed W, both positive entries decrease as σ increases up to half the normalized vertex total. Thus use σ=1−z, π=2+2z in the limit. Write D=2α/σ, B=(1−α)/√(σπ). We obtain

    liminf E⁵/t³ ≥ min (D⁴+4D²B²+2B⁴)/(8z),

where t=√(2n), 0<z<1 and 0≤α≤1. Set r=2(1+z)/(1−z)>2 and y=α/(1−α), including y=∞. The objective equals

    (r+2)^5 (8r²y⁴+8r y²+1) / [1024 r²(r−2)(1+y)^4].

At fixed r its derivative in y has the sign of 8r²y³−4ry²+4ry−1, strictly increasing for y≥0 and negative at zero. Thus the unique minimum satisfies v=2ry and r=v²(1−v)/(2v−1). This r decreases with v between 1/2 and 0.54 (its value at 0.54 is below two). Substitution gives

    F(v)=−(v³−v²−4v+2)^5 /
          [128(2v−1)²(2v²−4v+1)³(v³−v²+4v−2)].

On the admissible interval F' has the opposite sign of

    P(v)=v⁶−4v⁵+16v⁴−31v³+34v²−19v+4.

Indeed direct differentiation gives F' equal to −P(v) times (4v²−5v+2)(v³−v²−4v+2)⁴ divided by 32(2v−1)³(2v²−4v+1)⁴(v³−v²+4v−2)². Setting x=v−1/2 gives P=1/64−21x/16+119x²/16−13x³/2+39x⁴/4−x⁵+x⁶, strictly decreasing on 0≤x≤0.04 (bound the positive derivative terms at 0.04). P changes sign between 0.5128 and 0.5129, both admissible. Write v* for its unique zero there. The exact coefficient is c*=2^(3/10) F(v*)^(1/5). Transfer to arbitrary minima follows unrestricted-matching-exponent.md.
