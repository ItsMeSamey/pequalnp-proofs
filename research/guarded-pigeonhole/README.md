# Linear polynomial-calculus degree at maximum hidden rank deficiency one

Over GF(2), there is an infinite family with one equation per variable of the form x_i((Mx)_i+b_i)=0 and one parity marker 1+ℓ·x=0. Every row and column of M has bounded weight, the marker has bounded weight, the maximum hidden rank deficiency is exactly one, and every polynomial-calculus refutation has degree at least linear in the number of variables. Every ordinary PC refutation also uses exponentially many monomial occurrences. The unmarked base is satisfiable and its affine consequence ℓ·x=0 also requires linear degree. The lower bound uses the published graph FPHP theorem; the compilation below is the additional argument.

## Compile a graph

Take a simple bipartite graph with P pigeons, P−1 holes, maximum degree D on both sides, and a matching covering every hole. Write u* for the sole unmatched pigeon. At each hole put the matched edge first, followed by all its other edges in any order. Make a variable x_e for every **nonfirst** edge. Thus there are N=|E|−(P−1) variables. Let z_e=x_e on those edges. For the first edge f at a hole, let p be its pigeon and define the affine expression z_f=1+Σ x_e over the other edges of p. Those other edges are all nonfirst since the distinguished edges form a matching.

For each nonfirst edge e impose x_e (Σ_{k preceding e at its hole} z_k)=0. The marker is 1+Σ_{e incident to u*} x_e=0. Each row contains at most 2D−3 variable terms before cancellations. Each x_e occurs in at most D−2 later prefix sums at its own hole and at most D−1 prefix sums at the unique hole matched to its own pigeon, if any. Thus degrees on both sides of the directed dependency matrix are bounded independently of N.

At each hole, a second edge with z=1 would have prefix sum exactly one, contradicting its equation. Therefore each hole has at most one selected edge. The chosen affine substitutions give odd parity at every matched pigeon; the marker gives odd parity also at u*. This would put at least P edges into P−1 holes. In the unmarked base the all-zero x assignment corresponds to the original matching. Every unmarked model corresponds bijectively to a matching of all pigeons except u*, since those P−1 pigeons already require every hole and hence get exactly one edge each. Every edge of u* is zero throughout this fiber.

Treat each product as a disjunction of two affine equalities and the marker as one affine equality. Any subfamily after deleting the marker has independent hidden representatives e_i from its distinct pivots. Therefore its deficiency is at most one even with the marker restored. The full family has N+1 members in dimension N and its pivot normals already have rank N. Its deficiency is exactly one.

## Degree-preserving simulation from functional graph PHP

Use ordinary polynomial calculus over GF(2) with Boolean axioms, and edge variables y_e equal to one when selected. Standard graph FPHP contains the pigeon clauses, pairwise hole exclusions, and pairwise same-pigeon functionality exclusions. The positive pigeon clause at p is represented by the product of (1+y_e) over its incident edges, and exclusions are y_e y_f. The published paper uses the opposite truth convention, which is equivalent: an affine variable flip preserves PC degree by simulating multiplication by 1+y with a multiplication by y and one addition. The same constant bound follows using complementarity axioms in PCR.

From the pigeon product derive L_p=1+Σ_{e at p} y_e at degree at most D. Expand the product; every term of degree ≥2 is a multiple of a functionality exclusion. Generate each such monomial by single-variable multiplications and add it to cancel the term. The marker maps to L_{u*}. For a nonfirst e with first predecessor f, interpret each network x as its original y on that edge. Its guard polynomial in these source variables equals

    Σ_{k preceding e} y_e y_k  +  y_e L_{p(f)}.

Indeed, the last summand replaces the first edge variable y_f by one plus the sum of its pigeon's other edge variables. Every prefix summand is a hole exclusion, and multiplying the already derived linear row L by y_e has degree two. Boolean axioms for the surviving variables are source Boolean axioms. Now append a proposed ordinary network refutation line for line using its variable embedding. For network degree h the source derivation has degree at most max(D,h). This is a one-way simulation; treating parity alone as equivalent to functionality would be unjustified.

[Mikša and Nordström, Theorem 4.9](https://arxiv.org/pdf/1505.01358) prove over arbitrary fields that functional graph PHP on an (s,δ) unique-neighbor expander of maximum left degree D needs degree strictly greater than δs/(2D). Hence for s proportional to P and bounded D, the network needs Ω(P) degree. A squarefree Boolean-quotient PC derivation of degree h, including multiplications retaining degree h after multilinearization, lifts to ordinary PC degree at most h+1: the raw one-variable product has degree at most h+1 and each repeated factor is removed using a monomial multiple of a Boolean axiom at that degree. Thus the linear lower bound applies in that convention too. If the unmarked base derived ℓ·x at smaller degree, adding the marker would give a refutation at that degree.

The published PCR size lower bound also transfers to ordinary PC on the network. In the paper's truth convention, use a formal complemented PCR variable for each selected-edge bit y. Complementarity rewrites the bounded-width pigeon axiom as the product of (1+y_e) at constant cost per pigeon. The preceding row derivations then cost O(P) monomial occurrences in total for fixed D. Appending the network proof is a literal renaming into these formal variables, avoiding an expansion of all high-degree network lines under affine flips. A network refutation of monomial size S would give a source PCR refutation of size S+O(P), contradicting the exponential size lower bound unless S is exponential in N. This argument concerns ordinary PC. The separate degree lifting above already suffices for the quotient lower bound.

## Bounded-degree graphs with the required matching

Let P be large and superimpose eight independent random perfect matchings between two P-element sets. For fixed s≤γP the probability of any s left vertices having all their neighbors in 6s right vertices is at most

    binom(P,s) binom(P,6s) (6s/P)^(8s) ≤ (36 exp(7) s/P)^s.

The containment probability uses sampling without replacement in each permutation. Fix γ>0 with 6γ<1 and 36 exp(7)γ<1/2. The sum over s≤√P tends to zero by bounding the base by 36 exp(7)/√P. The remaining tail tends to zero by a geometric-series bound with base 1/2. Therefore graphs with more than 6s distinct neighbors for every such set exist. In the original multigraph, 8s incident half-edges and more than 6s distinct neighbors imply more than 4s neighbors touched exactly once. Collapse parallel edges and delete one right vertex. At most one of these witnesses is lost, so boundary size is at least 3s. Restricting any one of the original permutations to the surviving holes supplies the required matching. Every degree is at most eight, and every left vertex retains at least six neighbors by the singleton bound. Thus N is Θ(P) and s=floor(γP) yields the claimed linear bound. This is an existence argument, not a deterministic explicit expander construction.

## Local checks

Run python check.py. It checks each source-to-target polynomial identity symbolically on all qualifying simple 4-by-3 graphs with one fixed matching, then compares every Boolean model with the matching interpretation. These finite checks cover the compiler and its fiber, not the external expander lower-bound theorem.

## A polynomial-size linear program refutes the same family

For the odd marker ℓ·x=1, the relaxation reads only M, b and ℓ. Give each distinct mask a among the row masks aᵢ, the masks aᵢ+eᵢ, and the marker ℓ a variable zₐ in [0,1]. Bound xᵢ in [0,1]. Impose zₐ ≤ Σ_{j∈a}xⱼ, z_ℓ=1, and z_{eᵢ}=xᵢ whenever that singleton is present. For each pivot impose the real equality

    z_(aᵢ+eᵢ) − z_(aᵢ) = (−1)^bᵢ xᵢ.

On a Boolean model interpret zₐ as parity on a. Flipping coordinate i in the mask leaves parity unchanged when xᵢ=0. When xᵢ=1 the guard fixes the old parity to bᵢ, giving the displayed difference. Thus infeasibility certifies unsatisfiability. The LP has at most 2N+1 parity variables and polynomially many coefficients.

In the pigeonhole construction bᵢ=1. For hole h let B_h be the nonfirst edges of its matched pigeon. The row masks along the hole are successive prefixes starting at B_h. The edge equations telescope, giving Σ_{i nonfirst at h} xᵢ ≤ z_{B_h} ≤ Σ_{j∈B_h}xⱼ. For a hole without nonfirst edges the required 0≤Σ_{j∈B_h}xⱼ follows from nonnegativity. Summing counts every variable once on the left, while the disjoint supports on the right omit all edges of the unmatched pigeon. Subtracting common terms shows that the sum over the unmatched pigeon’s edges is zero. The marker requires it to be at least one. The graph exhibits a short contradiction certificate. The generic LP uses no supplied graph or matching.

For a limitation take a four-cycle, with row masks the two neighbors of each vertex, all offsets one and an odd total parity marker. Each selected vertex must have odd induced degree, contradicting the handshake lemma for odd cardinality. Yet setting every xᵢ to 1/2, the two-vertex masks to one, the three-vertex masks to 1/2 and the marker mask to one satisfies the LP.

The [LP checker](mask_lp.py) sums inequalities to obtain −1≥0 on 512 test graphs and verifies the rational cycle solution. The [Lean proof](../../lean/Research/AffinePigeonhole.lean) verifies the equivalence of the prefix condition and at-most-one, and the pigeonhole cardinality contradiction. The asymptotic result uses the cited external theorem and the simulation above.

[Two sparse modifications](separations.md) preserve the polynomial-calculus lower bounds and admit exact fractional solutions to the mask LP. Local distributions that agree on full bag intersections refute both modifications.
