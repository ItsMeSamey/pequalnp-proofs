# Refutation degree for bipartite even-degree guards with three markers

Polynomial calculus here is ordinary PC over GF(2), with Boolean axioms x_i²+x_i, guard axioms x_i(Ax)_i, and marker axioms Lx+b. The degree of a proof is the largest total degree of any line before multilinear reduction.

**Eight vertices suffice and are necessary for degree three.** Take four left and four right vertices. With right vertex 0 the low bit, the four left adjacency masks are 13, 3, 6, 10. The three-bit column labels, in left then right order, are 1, 5, 0, 5, 2, 6, 2, 0. The target is 3. Direct enumeration rejects all 256 assignments. Degree-two closure omits 1; degree-three closure contains 1. Run `python -B verify.py` to check this example with two implementations, one retaining ordinary monomial powers and one using squarefree monomials.

**Exact bounded-degree test.** Order squarefree monomials by degree with the largest degree leading. Keep an echelon basis of polynomial consequences up to degree d. On inserting a new independent row, multiply it by each variable if its degree is strictly below d, reduce squares, and enqueue each product. Addition and these multiplications suffice: in an echelon basis any degree-bounded subspace cut is spanned by exactly the pivot rows below the cut. At termination the entire span is closed under all permitted multiplications, including those following degree-lowering cancellations. Reduction to squarefree form is valid at the ordinary degree bound. Each square replacement is a Boolean axiom times a monomial of total product degree at most the original degree. Conversely, reducing every line of an ordinary proof preserves additions and normalized products; a raw line multiplied within the bound had degree strictly below d. Thus this is an exact decision procedure for ordinary PC degree. Failure at a finite bound is a lower bound even on dynamic derivations.

**Minimality.** The seven-vertex checker enumerates every bipartite graph, up to permutations inside the chosen sides, for side sizes 1+6, 2+5, and 3+4. An edgeless graph is included. For each graph it enumerates all 11,811 reduced row-echelon bases of rank-three marker row spaces and all eight transformed right-hand sides. This suffices since invertible row operations preserve the same degree-one consequences. Feasible supports are independently enumerated. The 102,414 NO representatives all refute at degree at most two. Isolated zero-label vertices pad every smaller instance; specializing them back to zero preserves degree bounds. Compile with `c++ -O3 -std=c++17 seven.cpp -o /tmp/pc-seven` and run `/tmp/pc-seven`. The six-vertex Python enumeration in `small.py` also covers ranks one and two.

For fewer than three independent markers, an inconsistent linear system refutes at degree one. In rank two, any nonzero target present as a column is feasible as a singleton. Otherwise, attaining the target requires odd counts in the two complementary nonzero classes A,B. A missing A–B edge gives a witness pair; a component of zero-label vertices touching both gives an induced cycle by taking a shortest path from A to B with nonempty zero interior and restoring the A–B edge. In a NO instance the A–B block is complete and no zero component touches both. Choose a cut separating A from B and putting each zero component on the side it touches, choosing either side for isolated components. The sum of guards over one side equals the product of the selected A and B counts. The marker equations force each count to equal one, proving 1 at degree two. Empty classes give a linear contradiction.

**Forests.** With k linear markers any NO forest refutes at degree at most max(2,k). Each edge monomial is derivable at degree two: peel leaves successively and subtract already derived incident edge monomials from the guard at each current leaf. The multilinear polynomial F equal to the product over the k markers of (1+marker axiom) satisfies F+1=0 derivably at degree k by telescoping partial products and multiplying marker axioms by the preceding factors. The coefficient of monomial S in F is the parity of the subsets of S hitting the requested marker value. If that coefficient is nonzero then some target-hitting subset of S contains an edge, since an independent set would be a feasible witness. Every monomial of F is therefore a multiple of a derived edge monomial, so F=0 follows within the claimed bound.

**A general bound using private marker equations.** Suppose the left side has k vertices and t is the rank of the full marker map minus the dimension of the right column span. The marker equations supply t independent affine equations exclusively on the left. An inconsistent marker system already refutes at degree one. Otherwise solve these equations, leaving s=k−t free left variables. A substituted guard is still of the form g(left)h(right), with g affine. The substituted guards are derivable from the initial axioms at degree two, since replacing a factor using a linear marker equation costs at most degree two.

Fix an assignment a to the free left variables and write D for its indicator. When g(a)=0 the conditioned guard imposes nothing. If g(a)=1 and g is nonconstant, complete its linear part to a basis of the s dual coordinates. Choose the s−1 other affine literals to test equality to their values at a. Multiplying the guard by those s−1 literals derives Dh, because the product of g and the literals is exactly D in the Boolean ring. This costs degree at most s+1. For g identically one, multiply the linear equation h by D within the same bound. For each remaining affine marker equation multiply by D to derive D times the conditioned marker, using Boolean reduction. The conditioned system on the right consists of inconsistent affine equations, so a linear combination of their D multiples gives D. Sum over a to obtain 1. This proves the bound max(2,k−t+1), also valid upon exchanging sides. A full-rank three-marker NO target lies outside each side's span and therefore has t at least one on both sides. In particular degree at most max(2, smaller side size) suffices. A uniform bound for arbitrary side sizes remains open here.

**Eight-vertex exhaustive check.** The companion `eight.cpp` tests all 97,155 rank-three RREF charts at balanced and unbalanced splits of eight vertices. Of 1,209,692 NO representatives, 312 need degree three and the rest refute by degree two. All 312 occur on 4+4 splits. Each representative passed its degree-three test. Consequently any degree-four example has at least nine vertices. Compile and run analogously to `seven.cpp`; the eight-vertex checker uses the GCC/Clang unsigned 128-bit integer extension.

**An algebraic certificate for the eight-vertex example.** Index the rows and vertices 0 through 7 and use free variables (a,b,c,d,e)=(x2,x3,x5,x6,x7). The markers give x0=1+c, x1=b+c, and x4=1+c+d. Write q0 through q7 for the eight guards after substitution and squarefree reduction. Encode monomials by the bit masks of their variable sets in the displayed free-variable order, with mask 0 denoting the constant. Their nonzero terms are respectively

```
q0   0 4 16 20
q1   2 4 10 12
q2   5 9
q3   6 18
q4   0 2 4 6 8 10
q5   4 5
q6   8 9 12
q7   16 18 20
```

The full coefficient row rank and the rank restricted to the quadratic columns are both seven. Thus their span contains no nonzero polynomial of degree below two and degree-two PC is already at a fixed point after eliminating the markers. Any original degree-two proof specializes under the affine substitution to a degree-two proof of this reduced system, since Boolean axioms of affine forms reduce to zero. For the upper bound, the following identity in the Boolean ring gives a degree-three refutation directly:

```
1 = q0 + q5 + q7 + a q6 + b(q3 + q4 + q7) + c(q2 + q3).
```

To lift this identity back to the original system, use the marker equations to derive the substituted guards in place of the original guards; replacing a factor of a quadratic product by its affine expression costs degree at most two.

## Private marker masks and the nine-vertex census

In any consistent full-rank NO instance the requested label is outside the span of the columns on each side: a subset of a single side is independent and hence feasible. Choose a functional vanishing on the right column span and taking value one at the target, and a second vanishing on the left span and taking value one there. They are independent because a common nonzero functional cannot vanish on the full rank-three column span. Complete these to a basis with third functional taking value zero at the target. Thus the output coordinates can always be chosen as a nonempty private mask alpha on the left, a nonempty private mask beta on the right, and an arbitrary third mask h, with required bits 1,1,0.

For a fixed graph, alpha, and beta, enumerate the feasible supports having both private bits one. If there is none, the two private equations alone refute at degree two. Otherwise choose one such support s. A full-rank third equation gives a NO chart precisely when h is independent of alpha,beta, has h·s=1, and annihilates the differences of all supports in that fiber. Compute an echelon basis of the difference span. If it has dimension n−2 the two private masks already span its annihilator and there is no remaining full-rank chart. Masks h and h+alpha+beta give equivalent systems with the same right-hand side. The counts below quotient by this equivalence; different private masks can describe equivalent charts.

Compile `c++ -O3 -std=c++17 private-hull.cpp -o /tmp/pc-hull` and run it with each split size 1 through 4 as its one argument. At nine vertices there are 9, 70, 386, and 1,053 graph representatives respectively. Nonempty-private-fiber NO charts checked number 41,642, 300,768, 1,002,069, and 2,015,072. Exactly 3,524 require degree three, all on the 4+5 split. Every remaining case refutes within degree two. The rank-less-than-three and inconsistent cases are covered above. Thus any degree-four example has at least ten vertices.

**Static cubic certificates can fail.** A 4+5 example has row masks 29,9,27,30, labels 0,1,1,4 on the left and 2,6,6,2,6 on the right, target 3. Eliminate the three marker equations. In the remaining six variables the reduced guards span dimension eight. One simultaneous multiplication sweep by all variables gives rank 38 among the 42 squarefree monomials of degree at most three, and the row span excludes 1. The next sweep on all degree-at-most-two consequences gives rank 42. Hence no static degree-three certificate exists, even though dynamic degree-three polynomial calculus refutes this instance. The ordinary-ring checker independently rules out degree two and confirms degree three.

At ten vertices compile the same checker with `-DPC_VERTICES=10` and run split arguments 1 through 5. The completed census gives the table below. The 32-bit free-edge encodings and 128-bit reduced-cubic coefficients suffice at these sizes.

| Smaller side | Graph representatives | Empty private fibers | Nonempty-fiber NO charts tested | Degree-three charts |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 10 | 1,013 | 170,154 | 0 |
| 2 | 95 | 4,128 | 1,273,994 | 0 |
| 3 | 734 | 16,706 | 4,787,974 | 0 |
| 4 | 3,250 | 52,780 | 12,438,735 | 29,504 |
| 5 | 5,624 | 82,827 | 17,731,166 | 76,964 |

Every ten-vertex NO case refutes at degree at most three. Thus a degree-four example requires at least eleven vertices.
