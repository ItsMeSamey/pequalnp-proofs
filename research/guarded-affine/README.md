# Eliminating guarded affine choices

Work over the two-element field. Each hidden decision bit z may be zero for every earlier assignment. It may be one if at least one affine literal in its guard holds. A guard may mention observed inputs, earlier decisions, and z itself evaluated at one. Finally, b terminal clauses must hold, each a disjunction of affine literals.

**Projection theorem.** The accepted inputs form a union of affine flats of codimension at most b. A uniform compiler represents acceptance as a disjunction of multilinear polynomials of degree at most b. It takes polynomial time for fixed b, even with arbitrarily many hidden bits. Given f feedback bits whose removal makes the dependencies acyclic, replace b by b+f and multiply the runtime bound by 2^f.

## Polynomial compiler

Choose one true affine literal per terminal clause. The product of those literals is one exactly when they all hold. The disjunction of all these products gives the target. Build the products one clause at a time and retain a basis of their linear span after each step. Replacing a family with a basis preserves the predicate that at least one member evaluates to one.

For one hidden bit write a polynomial uniquely as P₀ + zP₁ in Boolean multilinear form. The zero branch always provides P₀. When that is zero, the one branch succeeds just when P₁ and some guard literal g are one. Replace P by P₀ and all the products gP₁. The degree drops by one in P₁ and increases by at most one in each product. Iterate in reverse decision order, reducing to a basis between stages. For N total bits the basis dimension is at most the sum of binomial(N,j) over j≤b. Generation of candidates and row reduction take polynomial time in the input length and this dimension.

For a supplied feedback set, enumerate its assignments. Each fixed bit set to one contributes its guard as an extra terminal clause. Each other feedback guard holds automatically. Specialize their values, compile the acyclic remainder and take the disjunction.

## Flat codimension

Initially each selection of terminal literals gives an affine flat of codimension at most b, possibly empty. Eliminate the last decision z from one nonempty flat R. If its equations ignore z, choose z=0. Otherwise the projection of R has codimension one less than R, with a unique z above each projected point. Keep the slice at z=0. For each guard literal g also keep the intersection of the projection with g evaluated at z=1. Points with unique lift z=1 then survive exactly when a guard holds. Points with unique lift z=0 are already admissible. No new piece has codimension greater than that of R. Repetition proves the theorem. The list of flats can be exponential.

## A sharp limit on inner product

For f(a,b) = Σ aᵢbᵢ on two n-bit inputs, n≥1, the minimum number of acyclic terminal clauses is **exactly n+1**. Even with feedback, the number of terminal clauses plus the number of feedback bits is at least n+1.

On a flat v+U where f is one, the polar form B(x,y)=f(x+y)+f(x)+f(y) vanishes on U×U. This form pairs the two n-bit blocks nondegenerately. Hence dim U≤n. If dim U=n, its orthogonal complement equals U. On every coset of U the restriction of f is affine. Exactly one coset has constant restriction, since the map sending a coset represented by v to the linear form B(v,·) on U is a bijection. Every other coset contributes zero to the sign sum of f. Summing first over the second input shows the total sign sum is +2ⁿ. The constant coset therefore has value zero. For each nonzero a, fixing a and imposing a·b=1 gives a flat of dimension n−1. The largest one-flats thus have codimension n+1. The smallest exact cover of the one-set has 2ⁿ−1 pieces, by counting the points and using these disjoint fibers.

For the matching construction introduce hidden zᵢ guarded by bᵢ. Use one terminal clause per i requiring either bᵢ=0 or zᵢ=aᵢ. Together these conditions force zᵢ=aᵢbᵢ. The last terminal requires Σzᵢ=1. The construction has linear size and a unique extension on each accepted input.

This encoding also applies to XOR/AND circuits with affine constants. Each AND uses one guarded decision and one terminal clause. Substitute affine expressions for XOR wires, then impose the output as one more terminal. A lower bound t on the number of terminal clauses gives an AND-gate lower bound of t−1 in this basis. A codimension bound alone reaches at most the number of observed bits.

## Witness search and verification

A forward algorithm keeps actual assignments whose vectors of monomial evaluations through degree b span those of all reachable prefixes. Extend the representatives by zero, and also by one when feasible, then select a new basis. For each guard g the difference between its admissible one-extension and its zero-extension is a linear image of the old evaluation vector. Its nonzero block lists g times each monomial through degree b−1. The image is zero when g is false. Taking all guards proves the span invariant. At the last stage a satisfying witness makes the product of one literal per terminal nonzero, so some retained assignment does too.

The executable checked 800 feedback instances, 5,090 projected observations and every hidden assignment in the inner-product construction through n=4. Lean proves the pivot identity and the degree bounds. The flat theorem, complexity bound and sharp inner-product bound are mathematical proofs above. [Compiler](project.py) · [Witness search](solve.py) · [Tests](check.py) · [Lean proof](../../lean/Research/GuardRelease.lean)

## A cyclic case with no bound on component size

With one alternative per guard, absorb its offset into the diagonal to write the constraints as xᵢ(Ax)ᵢ=0. Suppose A is symmetric. Mark vertices with diagonal one, and join vertices when the off-diagonal entry is one. The linear span of feasible assignments consists exactly of the vectors selecting an even number of marked vertices in each connected component.

Sum the guard equations within a component. Each off-diagonal term occurs twice, proving necessity. Conversely every unmarked singleton is feasible. Join two marked vertices through unmarked vertices, using a shortest such path to eliminate chords. Its indicator is feasible because its endpoints have odd induced degree and its internal vertices even degree. Subtracting internal singletons puts the endpoint pair in the span. The graph on marked vertices joined in this way is connected within each original component that contains a marked vertex. Endpoint pairs therefore span its even-parity subspace.

For a final disjunction of affine literals, a literal true at zero needs no search. For a homogeneous literal, first test the unmarked singletons. If all fail, a witness exists precisely when the literal labels two marked vertices differently in the same component. A shortest path between differently labeled marked vertices is induced, has unmarked interior and itself witnesses that literal. An exhaustive comparison checked all 16,932 symmetric matrix and homogeneous marker pairs in dimensions one through four. [Solver and checks](symmetric.py)

## Removing the cycle assumption from the flat theorem

The codimension bound b also holds for arbitrary cyclic dependencies. The hidden assignment on each flat is a single affine map of the observations. Given a satisfying assignment, such a map through that assignment can be computed in polynomial time.

Fix a model. For each inactive hidden bit choose yᵢ=0. For each active bit take a guard literal gᵢ true at the model. Either equation gᵢ=1 or gᵢ+(1+yᵢ)=1 ensures its guard clause and passes through the given model. Their coefficient rows differ only at diagonal entry i. In the hidden coefficient matrix switch the active diagonal entries so the matrix becomes invertible. In elimination order each unused switch flips its current pivot. An inactive row is a unit row and retains its pivot one. Clearing below successive pivots gives a unit upper triangular matrix. Solving yields an affine map y(X) through the given witness. It satisfies all original guards on every observed input. Choose one true literal per terminal clause at the witness and substitute y(X). The resulting consistent system of at most b affine equations defines the promised flat. This strengthens the inner-product lower bound to b≥n+1 for cyclic guards as well. Locating a witness remains a separate search problem.

More generally, consider m clauses of affine literals. Let ρ be the maximum number of independent hidden normals one can select from distinct clauses. Use such a selection of affine literals, complemented to match the pivot convention, as ρ hidden coordinates. Complete the change of basis and fix the remaining coordinates to their witness values. Apply diagonal completion to the matched clauses and use one true literal for each remaining clause. Every accepted observation therefore lies on a flat of codimension at most m−ρ with an affine witness map. Every existential affine-clause encoding of inner product requires m−ρ≥n+1.

Lemma 3 of the November 2026 preprint by OpenAI Codex and Yichuan Wang already uses true linear combinations and an independent transversal. The observed-flat conclusion above specializes that mechanism to hidden normals. Theorem 1 of the preprint gives a one-sided randomized witness algorithm parameterized by maximum rank deficiency. The explicit diagonal construction here starts from a supplied witness. [Paper, Lemma 3 and Theorem 1](https://airaxiv.com/papers/pdf/2611.0031/?t=1795383815&v=1)

The checker constructed 2,843 charts and checked all 30,500 chart/input pairs, including guard satisfaction outside the terminal flat and recovery of the original witness. Lean checks invertible diagonal completion in every dimension and a single inverse for all right-hand sides. [Construction](charts.py) · [Checks](check_charts.py) · [Lean matrix theorem](../../lean/Research/DiagonalCompletion.lean)

## How many affine witness maps suffice?

With p observed bits and deficiency k, at most D = Σ_{j≤k} binomial(p,j) of these maps suffice for all accepted inputs. Each map has a certified domain described by at most k affine equations. Its indicator is their product and has multilinear degree at most k. Take a basis from the family of domain indicators for all witnesses. If a witness domain contains an input, evaluation there cannot vanish on every basis member. A retained map supplies a witness at that input. The bound counts actual maps and their domains. Selecting this basis efficiently requires access to the maps.

For k=1 an oracle finding a witness subject to affine restrictions on observed bits suffices to construct the list in at most p+2 calls. Start with the entire observed space as uncovered. A returned witness gives a chart whose domain is an affine hyperplane or the whole space. Intersect the uncovered space with its complement. This is empty or an affine space of strictly smaller dimension, since the witness was in the uncovered space. Stop on an empty space or when the oracle reports that it contains no feasible observation. Affine parameterization implements the restriction without changing the independent hidden representatives. This gives a search-to-compilation reduction at deficiency one. Correct rejection by the oracle is part of the hypothesis.

The Lean chart theorem recovers the supplied witness and satisfies the selected active guard at every observation, including cyclic dependencies. The tableau argument bounds the codimension of an accepting flat by the sum of path ANDs, parity tests and leaf deficiency. Its finite checker verifies the projected inner-product coset counts through three pairs. [Cyclic guard chart](../../lean/Research/CyclicGuardChart.lean) · [Tableau and preprocessing proofs](tableau-deficiency.md)

The [sparse interpolation solver](../sparse-marker/README.md) is deterministic given a polynomial support bound. The [rank-two defect analysis](../rank-two-defect/README.md) gives a polynomial hyperbolic case and a reduction equivalence with alternating three-marker feasibility.

The [occurrence-weight polynomial](../roabp/README.md) can have exponential ordered branching-program width in every variable order. A separate [three-color solver](../three-colors/README.md) decides simultaneous odd counts for its stated alternating guard class.

A [parity matching reduction](../trail-matching/README.md) solves eligible guarded trail presentations, with exact assignment checks through three variables.

The [anchor-completion algorithm](../anchor-completion/README.md) counts models with bounded cross-tree coupling rank. Without that rank bound, even the specified depth-one class is #P-hard.
