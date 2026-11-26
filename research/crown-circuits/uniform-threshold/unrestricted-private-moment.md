# Optimizing the two independent receiver class caps

The class bounds proven in unrestricted-private-pins.md give the general unrestricted lower coefficient c≈1.15238806926. Along a regular sequence attaining the unrestricted liminf, its final receiver graph has g∼h edges, at most (1−z+o(1))E shared columns and at most (1+z+o(1))E private columns. Pad the two classes separately with isolates up to these bounds. The argument of unrestricted-block-moment.md then gives

    liminf E⁵/t³ ≥ min (D⁴+4D²B²+2B⁴)/(8z),

with σ=1−z, π=1+z, D=2α/σ, B=(1−α)/√(σπ), 0<z<1 and 0≤α≤1. The endpoints z=0,1 are excluded already by unrestricted-shared-cover.md. Write r=π/σ=(1+z)/(1−z), y=α/(1−α). The objective is (r+1)^5(8r²y⁴+8r y²+1)/[64r²(r−1)(1+y)^4]. Its minimization in y is identical to the earlier case: v=2ry satisfies r=v²(1−v)/(2v−1), a decreasing function, now on its subinterval with r>1, inside (1/2,0.58). The substituted objective is

    F(v)=−(v³−v²−2v+1)^5/[8(2v−1)²(2v²−4v+1)³(v³−v²+2v−1)].

The derivative is −P(v) times (4v²−5v+2)(v³−v²−2v+1)^4 divided by 4(2v−1)³(2v²−4v+1)^4(v³−v²+2v−1)², with

    P=2v⁶−8v⁵+20v⁴−32v³+26v²−11v+2.

Setting x=v−1/2 gives P=1/32−9x/8−x²/8−7x³+15x⁴/2−2x⁵+2x⁶, strictly decreasing for 0≤x≤0.08 since −9/8+30(0.08)³+12(0.08)⁵<0. It has a unique admissible zero v* between 0.5275 and 0.5276. The exact lower coefficient multiplying n^(3/10) is 2^(3/10) F(v*)^(1/5).
