# Exact degree of three-pin cofactor tests

Fix a binary completion M of the physical graph and three named pins P. For each pair of equal-size subsets R,C⊆P record the determinant after removing rows R and columns C, identifying transpose pairs. These 14 binary entries include det M. A fixed completion succeeds if it is invertible and flipping any named diagonal alone destroys invertibility. An exterior succeeds if some choice of the three pin diagonals succeeds.

No polynomial of degree at most two over the binary field in these 14 entries vanishes on all unsuccessful states and is one on even one successful state, for either success predicate. This holds on a single 17-vertex original graph, even for polynomials chosen for that graph. Hence a list of such one-sided tests cannot detect success. Three factors suffice at a fixed assignment or, by enumerating eight named choices, to test a given exterior. Exterior search remains separate.

## Upper bound

Write a=det M, b=det M[−P,−P] and c_ij=adj(M)_ij. Fixed success is a times the product of the three c_ii, since a single flip adds c_ii. Jacobi's complementary-minor identity gives det(adj(M)[P,P])=a²b, including singular M by polynomial identity. In characteristic two the 3-cycles cancel. Evaluating the remaining terms at binary entries and multiplying by a gives the exact expression

    a b + a(c₁₁c₂₃+c₂₂c₁₃+c₃₃c₁₂).

Under another named diagonal choice each mixed minor is a linear combination of the same 14 minors. Expand in the updates on named sites retained as both row and column. Thus an OR of eight cubic tests decides exterior success. This does not bound the degree of their OR as a single polynomial.

## Finite calculation

By free-coordinate congruence eliminate the nonsingular free block. All mixed minors retain every free site on both sides and acquire the same unit determinant factor. If the remaining free radical fails to couple injectively to the pins all 14 minors vanish. Otherwise the radical has size t≤3, with independent binary rows L on the pins. Enumerate the border [0,L;Lᵀ,C] over these rows and all symmetric 3-by-3 C, including the all-zero state from deficient coupling. This exhausts 136 states. Lift each to its vector of squarefree monomials of degrees zero through k. Row-reduce the lifts of unsuccessful states. A successful lift belongs to their span exactly when no degree-k one-sided polynomial distinguishes it. The [calculation](mixed_principal_channels_check.py) gives (rank, number of successful rows in the span).

| Predicate | Degree 1 | Degree 2 | Degree 3 |
|---|---:|---:|---:|
| Fixed diagonal, eight successful states | (15,8) | (85,8) | (128,0) |
| Exterior, thirty successful states | (15,30) | (85,30) | (106,0) |

## One physical graph realizes the full test

Use three independent named vertices. For each of the seven nonzero binary 3-vectors v add two free vertices a_v,b_v joined by an edge, and join a_v to exactly the pins of v. Set the pin diagonals to zero. On (a_v,b_v) the diagonal choice 00 eliminates with zero update, 01 contributes vvᵀ, and 11 eliminates b_v and retains a radical row v with zero pin update. Install any independent row basis for L. The seven matrices vvᵀ span the symmetric 3-by-3 matrices by using the unit and doubleton vectors. For a vector v already used as a radical row, the missing update vvᵀ would preserve all mixed minors: adding that retained radical row to each retained pin row i with v_i=1 performs the update. A basis change among retained radical rows and columns also preserves the minors. Three dependent radical rows realize the all-zero state. The [original graph checker](universal_pin_boundary_check.py) directly evaluates the 14 raw determinants and eight named choices on all 2,187 assignments and compares with the complete reduced state set. It also obtains the 15 nonempty pure principal-deletion patterns from each parity class. The test concerns these determinant features. A search can use other data in the circuit or graph.
