# The fixed 35-state reservoir has an exact cubic decoder

In the [nine-added-vertex reduction](one-missing-reservoir-universality.md), use binary polynomial calculus with Boolean field equations and formal degree. Multiplication at degree D is allowed on a parent of degree at most D−1. For a literal three-pin NO instance with minimum refutation degree d≥2, the expanded graph has minimum degree d′ satisfying

    d ≤ d′ ≤ max(3,d).

Iterating this reduction cannot take a degree-three instance to degree four. The separate decoder itself needs degree three when the three input color parities are independent indeterminates.

## A finite derivation on nine indeterminates

Write b for the six inner selection bits and f,g,h for the three payload color parities. In the bit-mask convention of the reduction let X=(f,g,h), s=3+(X AND 5), t=7+(X shifted right one bit), with all vector additions binary. The six-site rows are the last six of (170,449,240,81,300,341,174,327,178). Their low three bits give vectors B_i, their high bits give rows J_i. The nine equations are the three components of s+Σ_i B_i b_i and the six products b_i(J_i·b+B_i·t).

The [reproducible elimination](reservoir_degree_decoder.py) gives the following exact ranks for the closure of those equations in squarefree binary polynomials. The last three columns test membership of the specific named rows.

| Degree | Rank | f | g | 1+h |
|---|---:|---:|---:|---:|
| 2 | 30 | no | no | no |
| 3 | 125 | yes | yes | yes |

Index subsets of nine bits of size at most D in increasing size and lexicographic order. For each subset S, form the nine-bit column equal to the XOR of the nine guard-value vectors at the indicator vectors of all T contained in S. Row reduce the resulting nine rows by their greatest pivot, placing each new row whose pivot has degree below D on a queue. For every queued row and each variable i, replace every monomial S in that row by its union with {i}, cancelling repeats, then insert the result. At exhaustion reduce each target row against the same pivots. Greatest-degree-first pivot reduction means the low-pivot rows span the entire subspace of eligible parents. Replacing a square by its variable uses a field equation within the unreduced product degree, so the computation constructs and exhausts the formal degree-bounded closure. The system is feasible, including X=4, b=9.

Summing all inner guards cancels the internal edges. The three pin rows then give s·t=f+g+fg at degree two. Multiplying by f and by g derives f and g at degree three. The final named consequence 1+h is certified by the same finite calculation and uses the particular missing inner state.

## Substitution and witness-level specialization

On the expanded host the displayed equations are its actual new pin equations and inner guards after substituting the three payload parities for f,g,h. Replacing an indeterminate by an affine linear form preserves formal polynomial-calculus degree over the binary field. A variable multiplication becomes a sum of variable multiplications and, if needed, the original row. The image of a Boolean field equation is a sum of Boolean field equations. Thus the decoded equalities f=g=0 and h=1 are available within degree three for every payload.

Write v_i=(a_i,b'_i,c_i) for the fixed three-bit color of payload site i and z_i for its selection. The difference between its expanded and old guard is the selected-site product with the toggled degree. Replacing the sender Σ B_i b_i by 7 costs a product of z_i with derived linear equations. On that sender, the added pin and reservoir drift is a_i+b'_i. The off-diagonal toggles contribute a_i f+b'_i g+(a_i+b'_i)z_i. Multiplication by z_i cancels the constant drift modulo its field equation and the two decoded zero parities. This derives every old quadratic guard within degree three. For literal pins the old colors are 1,2,7 on the three pins and zero otherwise. The decoded equalities give each old pin selection equal to one. Each old pinned output equation follows from its old guard using an affine multiplier on its derived linear pin equation. The old equations with pinned inputs substituted follow at degree three. An old refutation can resume from those derived rows without adding their derivation degree to its own.

Conversely, specialize the six inner variables to mask 9 and all three old pinned inputs to one. Their colors now sum to 4 identically. The new pin equations and inner guards vanish, and the surviving payload rows reduce precisely to the original free guards and original pin output equations, up to Boolean simplification. A lower-degree refutation on the host therefore specializes to one on the old graph. Using affine coordinates for the consistent old pin slice is equivalent at degree at least two: substitution of the affine parametrization is degree-preserving, and reversing it uses affine consequences of the original pin rows to recover the substituted quadratics with linear multipliers. Graph-specific simplifications can lower the degree needed for the decoder. Its degree-two negative tests apply to the displayed nine-indeterminate system. This result supplies no universal degree bound for arbitrary original hosts.
