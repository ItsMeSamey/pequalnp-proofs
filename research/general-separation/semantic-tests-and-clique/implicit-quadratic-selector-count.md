# Counting an implicit circuit after a quadratic map

Let Q have q input bits and r explicitly supplied Boolean quadratic outputs. Let H be a binary-gate Boolean DAG on those r coordinates with h gates. Coordinates may repeat and contain affine or constant terms. In an original DAG the frontier must separate primary inputs from the output, and its quadratic labels must be certified. Every basis change implemented inside H is charged to h.

Write P_s=s·Q, let B(s) be its alternating polar matrix, and set G(s)=Σ_x (−1)^{P_s(x)}, W(s)=Σ_y H(y)(−1)^{s·y}. Character orthogonality gives the count 2^{−r} Σ_s W(s)G(s). The one-selector cost T_H for W is bounded by two exact counts on the shared H with a parity test. Enumeration costs poly(r+h)2^r. Tseitin encoding gives O(r+h) variables and clauses of width at most three with unique extensions. Thus the pinned October fixed-density exact counter gives poly(r+h)2^{O((r+h)/√log(2+r+h))}, padding to fixed density and dividing out introduced free bits if necessary. Take the better bound or an available sound circuit-specific counter. Partial sums and products use O(q+r+1) bits. Alternating elimination and summation on the radical compute each quadratic Gauss sum in polynomial time.

## A support certificate

Fix d≥1. Find all maps D from selectors to q-bit directions whose coordinates have Boolean degree at most d and satisfy B(s)D(s)=0 identically. Equate multilinear coefficients. The left side has degree at most d+1 and is linear in the unknown coefficients of D. Linear algebra produces a basis D_j in polynomial time for fixed d. For each basis map form g_j(s)=P_s(D_j(s))+P_s(0), of degree at most 2d+1. A radical direction introduces only a constant derivative, so g_j(s)=1 implies G(s)=0 by translation. For fixed s, v ↦ P_s(v)+P_s(0) is linear on the radical. Thus the g from every allowable map belongs to the span of the g_j as a polynomial function.

Let S be the common zero set of the g_j, L=|S|, and J the number of nonzero Gauss sums on S. Zero belongs to S. Multiply each g_j by each selector coordinate in the Boolean ring, reducing squared bits. Intersect the span of the products and original equations with the degree-at-most-one polynomials by coefficient elimination. The resulting equations vanish on S and have zero constant term. If their rank is r−k, parameterize their kernel by k bits. The substituted equations still have degree at most 2d+1 and exactly L joint zeros.

For each fixed d there exists η_d>0 such that the count costs

poly(input size + q+r+h) · (2^{(1−η_d)k}(L+1)^{η_d} + J T_H).

The deterministic bounded-degree counting theorem of Lokshtanov, Paturi, Tamaki, Williams and Yu tests every prefix for extension in polynomial time times 2^{(1−η_d)(k−i)} on k−i free coordinates, shrinking η_d to absorb its lower-order term. Test children only of viable prefixes. Level i needs at most min(2^i,2L) tests. Summing the geometric series on either side of log₂(2L) gives the bound, including all L Gauss evaluations. Only J nonzero evaluations require H. Neither L nor J must be supplied. For k=0 no polynomial-system counter is needed. [Bounded-degree counting theorem 1.2](https://theory.stanford.edu/~yuhch123/files/polyEq.pdf) [October exact counting theorem](https://github.com/openai/math/blob/92b516ef8e/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex)

## A hidden quadratic permutation

For q=r=3t consider componentwise cubing on t copies of F₈. Cubing has quadratic Boolean coordinates and is a permutation since 3 is coprime to 7. Each block takes a constant number of binary gates. Use trace-dual selector coordinates, so P_s(x)=Σ_j Tr(s_j x_j³). The whole pencil has trivial common radical. For v_j nonzero there is an x_j outside {0,v_j} with x_jv_j(x_j+v_j) nonzero. A selector detects this polar value by nondegeneracy of trace.

For each j use the linear map D^{(j)}(s) with only jth entry s_j². Suppressing j, the coefficient of x in the traced polar is (sv)^4+sv², zero for v=s² since s^{12}=s^5 on F₈. Its constant derivative is Tr(s⁷)=1[s≠0]. Thus each block nonzero indicator lies in the span of the g_j. Every coordinate bit z in a block satisfies z=z·1[block≠0]. The degree-one multiplier step derives all r independent selector bits, hence k=0 and L=J=1. The answer is 2^{q−r}#H. One ordinary count suffices regardless of the outer spectrum. For example AND has one accepting assignment and every Walsh coefficient nonzero.

The same discovery holds for Q'(x)=UQ(Ax+a)+b under invertible binary linear changes A,U. Use directions A^{-1}D^{(j)}(Uᵀs). Their radical condition makes the input shift contribute zero polar derivative and the output offset cancels. The transformed bits are homogeneous linear combinations of s and yield all r independent equations. No block decomposition is supplied to the algorithm. Dense coordinate maps incur their actual encoding and gate costs.

## Affine versus quadratic selector dependence

Take one F₃₂ block with Q(x)=x³. For s≠0 the polar condition is (sv)^{16}+sv²=0. Squaring gives sv+s²v⁴=0, hence the radical is {0,s^{10}}. The function s↦s^{10}=s²s⁸ is a permutation and is quadratic. Its first derivative at increment 1 has nonconstant part x²+x⁸, which is not identically zero, so the function is not affine.

For an allowable affine map of rank j between one and four, every nonzero attained value has 2^{5−j} preimages, at most one of which can be nonzero. Thus the fiber size must equal two and every nonzero image value would need 0 in its fiber. Rank four has at least fifteen nonzero values, a contradiction. Rank zero allows only the zero map. A rank-five map differs from s^{10} at most at 0 and its unique zero. A differing coordinate of their difference has degree at most two and if nonzero has support at least 2^{5−2}=8, by the minimum-weight induction using a nonzero first derivative. Agreement everywhere would make s^{10} affine. Thus there are no nonzero affine sections. For products, fixing a nonzero local selector puts the image of the cross-block linear variation in its radical line. Intersecting these lines over local selectors leaves zero. Only local maps remain.

With d=2 the block section s^{10} has derivative Tr(s^{31})=1[s≠0]. The same multiplier step derives every selector equation, including after affine changes. These quadratic maps have linear gate size on arbitrarily many bits and separate d=1 from d=2 for this certificate.

## Dense support and a direct count

For q≥2 let Q(x)=(x₁,x₁x₂,…,x₁x_q). For every nonzero tail selector the slices x₁=0 and x₁=1 give G(s)=2^{q−1}, whereas G(0)=2^q and G(e₁)=0. Even perfect Gauss-support recognition leaves 2^q−1 selectors. Taking H to be AND makes every term at those selectors nonzero. Splitting the primary bit directly gives 2^{q−1}H(0)+#(H restricted to y₁=1). The identity frontier permits every H and can place all computational difficulty in the remaining count.

The unrestricted O(q log q)-gate CircuitSAT saving and uniform P versus NP remain open.
