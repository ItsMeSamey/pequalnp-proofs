# Existential projection at binary rank one and two

Over GF(2), residual clauses of hidden rank at most one admit a uniform polynomial-time compiler for exact existential projection. At hidden rank at most two, deciding the projected value at a supplied observation is NP-complete, even when the observed block is empty. Rank is measured **after** enforcing the affine equations and relative to the specified hidden variables.

## Input and rank

The input explicitly lists observed bits $X$, hidden bits $Y$, affine equations $AY=b+BX$, and clauses. Each literal is an affine form in $X,Y$ and is true when its value is one. A constant offset represents negation. The required output is a Boolean circuit on $X$ computing whether some $Y$ satisfies the input.

Row reduction gives an observed consistency condition $K(X)$. When it holds, write all hidden solutions as $Y=Y_0(X)+Nt$, where the columns of $N$ form a basis of the kernel of $A$. Each literal becomes $a_j(X)+u_j(t)$. The **hidden rank of a clause** is the dimension of the span of its linear forms $u_j$. It is independent of the kernel basis and computable from the input matrix.

## Rank one

In a rank-zero clause, check the observed disjunction directly. In a rank-one clause, every nonzero $u_j$ equals the same form $u$, since the field has two elements. At a fixed $X$, the clause already holds if an observed-only literal is true or if two occurrences of $u$ have opposite offsets. Otherwise their offsets agree on a bit $a$, and the clause requires exactly $u(t)=1+a$.

Let $d(X)$ indicate that this equation is required. Use the row $d(X)u(t)=d(X)(1+a)$, which becomes $0=0$ when inactive. The output is $K(X)$ conjoined with consistency of all these rows. To construct a single circuit for all observations, unroll Gaussian elimination with multiplexers selecting whether an incoming row installs a pivot, uses an existing pivot, or passes that pivot position. For $c$ such rows and $h$ hidden bits, this stage uses $O(c(h+1)^2)$ Boolean gates. Row reduction, substitution and construction of the observed offsets take polynomial time in the explicit input length. XOR gates can be expanded into a constant number of ordinary Boolean gates.

## Rank two

Reduce from 3-SAT. For each three-literal source clause introduce fresh bits $s_1,s_2,s_3$. Require odd parity $s_1+s_2+s_3=1$ and impose the implications $s_i⇒ℓ_i$ for its three literals. All source variables **and** all selectors are hidden. There are no observed variables.

A true clause extends by selecting just one true literal. A false clause forces all three selectors to zero and violates parity. Freshness makes the extensions independent across clauses. The reduction is linear in the source size, and checking a complete assignment is polynomial.

The parity equations use disjoint triples. Each binary implication is Horn because its selector appears negatively, so either sign of the source literal gives at most one positive literal. The graph formed by the binary clauses alone is a forest of stars, since each selector occurs once there. After affine substitution each binary clause contains at most two latent forms, giving rank at most two. A uniform polynomial-time compiler at this rank with polynomial-time evaluable output would decide 3-SAT by evaluating its zero-input output.

For a parsimonious variant add $s_i⇒¬ℓ_j$ whenever $j<i$. Exactly the earliest true literal is then eligible, so every satisfying source assignment has **one** selector extension. The new implications remain Horn and preserve the rank bound. The forest-of-stars claim applies to the base construction.

## Verification

The [Python checker](check_rank_projection.py) implements the compiler and compares its output with exhaustive hidden assignments, including clauses whose raw masks differ before row reduction. It also checks both reduction variants on every signed triple over two source variables. The [Lean file](../../lean/Research/RankOneProjection.lean) proves the guarded rank-one clause identity and the two selector equivalences for arbitrary indexed families of clauses. The compiler's size bound is proved above.
