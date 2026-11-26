# Indexed joint probabilities of clause violations

Use the uniform distribution on all assignments to a declared set of Boolean variables. Count the width after deduplicating literals. A tautological clause has violation probability zero, and an empty clause has probability one. For k≥1 let d=⌊log₂(k)⌋+2.

## Upper bound

For each index set J, write p(J) for the probability that every clause indexed by J is violated, with p(∅)=1. Compare two width-at-most-k indexed CNFs with equal p(J) for |J|≤d. A zero singleton identifies a tautology. Among the other clauses, prescribed violations are jointly feasible precisely when all pairs prescribe compatible values to every shared variable. Accordingly, a zero pair decides every larger joint probability containing it. Fix a remaining pairwise-compatible target family J. Every subfamily has positive joint probability. For T⊆J,

    u(T) = −log₂ p(T) = |⋃_{i∈T} scope(i)|.

For nonempty T of size at most d, inclusion-exclusion recovers the number of variables shared by every scope indexed by T as the sum over nonempty A⊆T of (−1)^{|A|+1}u(A).

Fix i∈J. For each variable in scope(i), form the Boolean membership vector recording which of the other scopes in J contain it. Its multiset has at most k entries. Multilinear moments of degree r≤d−1 of its counting measure are exactly the common-scope sizes for subfamilies consisting of the anchor and r other indices. They therefore agree in both formulas.

If a nonzero real signed measure on a Boolean cube annihilates all square-free monomials of degrees ≤r, each sign occurs at least 2^r times in its support. For r=0 total mass zero gives the result. For r>0 choose a coordinate varying on the nonzero support. Both slices are nonzero, and each slice annihilates degree ≤r−1 since its indicator is x_j or 1−x_j. Apply induction to each slice. In particular, for integer weights the positive and negative masses each total at least 2^r.

Apply the bound to the difference of the two anchored counting measures. Each sign has total mass at most k, whereas 2^{d−1}>k. Thus the measures coincide. Since this holds for every anchor, every nonempty incidence pattern on J has the same multiplicity in both formulas. Summing over these patterns gives equal union sizes and hence equal p(J). Möbius inversion recovers every atom of the joint Boolean violation vector. Model counts follow when the total numbers of declared variables agree.

## Matching lower bound for every k≥1

Put d=⌊log₂(k)⌋+2. Formula F_b has one variable x_S for each subset S⊆[d] with |S|≡b (mod 2), and clause i is the disjunction of x_S over S containing i. Each formula has n=2^{d−1} declared variables and all d clauses have width w=2^{d−2}≤k. An assignment with all clauses indexed by J violated may freely set exactly the variables x_S with S∩J=∅. If J is proper, [d]∖J is nonempty and has equally many even and odd subsets. This gives identical probabilities for all joints of size ≤d−1. For J=[d], exactly two assignments satisfy the simultaneous violation in F₀ and exactly one in F₁, because F₀ has the variable x_∅. Inclusion-exclusion gives

    #SAT(F₀) − #SAT(F₁) = (−1)^d.

Thus one fewer order cannot determine the distribution or the model count. Both formulas are satisfiable. When k≥2, an extra tautological clause on x_∅ in F₀ and on an arbitrary variable in F₁ makes every declared variable occur while preserving the argument. If width exactly k is required, add one disjoint k-literal positive clause with fresh variables to each formula, multiplying the discrepancy by 2^k−1 and retaining equality of the lower moments. These conventions are independent of the threshold proof.

## SAT status at small widths

For k=1 the two pairs of unit clauses (x),(x) and (x),(¬x) have equal singleton probabilities and opposite satisfiability. For k=2 or 3 use d=3 above, and include both the all-positive and the all-negative clause on each of the three scopes. Each scope now imposes a two-variable not-all-equal constraint. The even-parity scopes form the three edges of a triangle on x₁₂,x₁₃,x₂₃, so the CNF is unsatisfiable. The odd-parity scopes form a star centered on x₁₂₃, so the CNF is satisfiable. Each scope has size two and each two distinct scopes meet in one variable in both models. Same-sign joints of order two agree by union size, and opposite-sign joints vanish because the scopes meet. Adding a disjoint positive clause on three fresh variables gives maximum width exactly three if desired.

## Recovering a specified joint efficiently

The oracle returns the exact exponent of a nonzero low-order joint and flags a zero. For a compatible family J, choose an anchor clause i. Start with its width as the multiplicity of the empty membership pattern. Expose the remaining clause indices one at a time. If there are t distinct prefix patterns, let z be the t-vector of unknown counts taking bit one at the next coordinate j.

For each square-free monomial M on old coordinates, its evaluations on the known patterns, dotted with z, equal the intersection size of the scopes of i, j and the clauses in M. Monomials through degree r=floor(log₂ k) span every vector on the patterns. Otherwise a nonzero rational vector supported on at most k patterns would annihilate all low moments. The signed-support lemma requires at least 2^(r+1) support points.

Generate independent rows by degree layers. Start from the constant row. Multiply a basis of the preceding layer by each coordinate column, retaining independent rows along with the old basis. Repeated factors collapse by Boolean idempotence. This spans all rows of the new layer because multiplication distributes over linear combinations. Stop once t independent rows are collected. Each right-hand side uses at most 2^(r+2) ≤ 4k oracle calls by inclusion–exclusion. Solving the square system gives both new multiplicities for each prefix. At most k prefixes occur at every stage. Exact linear algebra has polynomial bit cost by the determinant bound for zero-one matrices of dimension at most k.

For each anchor, expose just the earlier clauses. The multiplicity of the all-zero prefix counts variables first seen at that anchor. Summing these counts recovers the union size. The algorithm runs in time and oracle queries polynomial in k and the size of J, even when k varies. Computing a satisfying probability still involves an outer sum over target families.

Python tests the query-order limit against direct scope unions and literal conflicts. Lean checks the integer trade bound. The algorithm and running time are justified above. [Implementation](indexed.py) · [Checks](check_indexed.py) · [Lean trade bound](../../lean/Research/MomentTrade.lean)
