# Unbounded separator degree on connected graphic one-hole traces

For n≥2 take binary graphic incidence columns on five protected vertices L,R,O,U,D and free vertices x₁,…,xₙ,y,z,w. The protected four-space T consists of even subsets of the five terminals. Prescribe color 0 on L,R,O and color 1 on U,D. Every extension d of this covector has a unique normalized coloring with those prescribed colors. The free colors are independent parameters.

Use ordinary edges Lxᵢ,Rxᵢ for every i, consecutive xᵢxᵢ₊₁, and xₙD, Uy, Uz, yx₁, zx₁, Ly, yO, Rz, zO, Dw, wR, wxₙ. A terminal set lies in the span of ordinary columns eligible under d exactly when it meets every monochromatic component evenly. The additional vertex w preserves monochromatic connectivity between old vertices: D and R have opposite colors, and both are already adjacent to xₙ.

Set g=y∨z=y+z+yz, Pᵢ=x₁⋯xᵢ, P=Pₙ, F=gP. The blue terminals U,D connect exactly when F=1 since a blue path needs y or z and every xᵢ. The red terminals L,R connect exactly when F=0. Any red xᵢ joins them; with all xᵢ blue the remaining red path requires y,O,z. Consequently p=L+R+U+D is absent. The other seven points of ker λ are attainable: for red-only fluxes 0, LR, LO, RO choose all free vertices red. For UD use all xᵢ,y,z blue. For LO+UD use all xᵢ blue, y red, z blue. Interchanging y,z attains RO+UD.

Any separator c(d) has c(p)=1 and vanishes on eligible edges. In vertex potentials, defined up to a common constant, this forces c(L)+c(R)=F. When F=0 the red path forces zero. When F=1 the blue path forces c(U)+c(D)=0, so the red difference equals one. The unique multilinear expression for F has degree n+2. Affine changes of free parameters and linear changes of output coordinates preserve the degree bound.

The following potentials attain it:
- c(R)=c(D)=c(w)=0, c(L)=F, c(U)=1+F;
- c(xᵢ)=g(Pᵢ+P);
- c(y)=y+F, c(z)=z(1+F), c(O)=(1+y)F.

Each eligible edge has equal endpoint potentials. For instance neighboring blue path vertices have equal prefix product; blue y or z implies g=1; red y gives c(O)=c(y)=F; red z makes (1+y)F=0 since g=y. The others follow directly. These formulas have degree at most n+2, so the minimum selector degree is exactly n+2 among n+3 free coordinates. Without w the bound reaches the full number of free coordinates.

The patched ordinary matroid is connected. Its K₂,ₙ core is biconnected; add the path edges, then ears L–y–x₁, R–z–x₁, y–O–z, y–U–z, xₙ–D–w–R and the remaining edge wxₙ. In the quotient by T all terminals become one hub. Deleting it leaves a connected path with y,z joined at x₁ and w at xₙ; deleting any other vertex leaves all remaining free vertices adjacent to the hub. Thus the quotient matroid is connected as well.

The Boolean circuit for the displayed selector has linear size despite the unbounded algebraic degree. More generally polynomial-size Boolean circuits can compute a candidate separator by Gaussian elimination on the eligible columns. Checking universal correctness still requires ruling out the target for every d.
