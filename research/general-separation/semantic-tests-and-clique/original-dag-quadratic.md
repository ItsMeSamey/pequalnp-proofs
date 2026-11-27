# Counting original gate DAGs with a sparse higher-degree remainder

The [runner](original_dag_quadratic.py) takes an unannotated topologically ordered two-input gate DAG with truth tables indexed by 2a+b. Over the Boolean ring GF(2)[x]/(xᵢ²−xᵢ), propagate the exact algebraic normal form (ANF) of each gate. A polynomial is a set of variable masks. For a product take mask unions and toggle repeated outputs. If a finished gate exceeds a caller-supplied cap C, return no result from this rule. With straightforward pair multiplication the preprocessing uses poly(q,s,C) time and space for s gates, including the temporary product with up to C² masks. A cap failure has no implication for satisfiability.

Write the surviving output as a quadratic Q plus the XOR of h monomials of degree at least three. Counter 1 greedily builds a set H of inputs meeting each high monomial in all but at most two positions: repeatedly choose a variable contained in the most currently unsatisfied residual masks. Pinning H gives 2^{|H|} quadratic residuals. Counter 2 expands the sign of the remainder using (−1)^M=1−2M. For each subset J of high monomials, force all variables in their union to one, and accumulate (−2)^{|J|} times the restricted quadratic sign sum. This gives 2^h quadratic residuals even for a single monomial of degree q. Select the cheaper certified bound. Convert the signed sum S to the number of satisfying assignments (2^q−S)/2.

For the quadratic residual take a pair with coefficient one and write Q=xy+xA+yB+C on the remaining variables, with A,B affine. Summing over x,y yields exactly 2(−1)^{C+AB}; the residual is quadratic. An affine sign sum is zero if any variable occurs and is otherwise ±2^{number of free variables}. The complete solver takes poly(q,s,C) times 2^{min(h,|H|)}; signed coefficients have polynomially many bits under the cap. This is a sufficient test on a particular presentation.

The finite corpus replaces each pair-product ab by ((a XOR cd)b) XOR (cdb), using distinct primary control bits c,d. The raw gate graph has cubic internal functions. Four variants add respectively no high term, a family of cubic monomials sharing x₀, the full degree-q monomial, or disjoint cubic monomials. All 12 counts were tested against independent exhaustive bitmap gate simulation at cap 32.

| q | Gates (clean/star/wide/disjoint) | Satisfying assignments | Quadratic residuals |
|---|---|---|---|
| 8 | 23 / 32 / 31 / 29 | 120 / 120 / 121 / 124 | 1 / 2 / 2 / 4 |
| 10 | 29 / 41 / 39 / 38 | 496 / 496 / 495 / 504 | 1 / 2 / 2 / 8 |
| 12 | 35 / 50 / 47 / 47 | 2016 / 2016 / 2017 / 2040 | 1 / 2 / 2 / 16 |

The peak gate ANF sizes at q=12 were 6, 11, 7 and 10 masks. The same independent oracle checked 120 seeded random DAGs of 2–8 inputs. Residual counts measure calls to quadratic elimination; exhaustive simulation was used solely as the finite correctness oracle. Disjoint cubic terms increase the branch exponent to floor(q/3) in the control family. Dense intermediate ANFs can stop the rule earlier.
