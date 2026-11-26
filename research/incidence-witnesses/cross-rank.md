# The two mixed cuts of the polarized quartic tensor

Separate the two point slots and two line slots into four variable groups. The coefficient tensor has entry one when the two point and two line addresses are distinct and induce a matching, and zero otherwise. It is the negative of the mixed coefficient tensor obtained by substituting the sum of the two point-variable copies and the sum of the two line-variable copies in the multilinear incidence polynomial.

For the cut joining one point slot and one line slot on each side, the matrix has N² rows and N² columns. Its determinant in absolute value is

    (q+1) q^{N(N−1)−2q³+3N}.

Order the addresses (p,l) by whether p is incident to l. The cross matrix is block diagonal since a matching must pair both points to their own line slots or both to the opposite slots. For two flags (p,l),(r,j) the entry is one precisely when p∉j and r∉l. Write S for the flag switch changing the line while fixing the point, and T for the switch changing the point while fixing the line. Each switch is a direct sum of N copies of J−I of order q+1. The flag block is STS. Indeed its three-step walk must use the intermediate line pr, which exists uniquely when the flags are opposite. For all other flag pairs no such walk exists. Hence the absolute flag determinant is q^{3N}.

On nonincident addresses the complementary block D is the corresponding principal minor of the matrix L with entries A[p,j]A[r,l], where A is the point-line incidence matrix. The zero diagonal for repeated point or line slots is automatic on this block. As a linear map L acts by X↦AXᵀA. Since AAᵀ=qI+J, its determinant has absolute value (q+1)^{2N} q^{N(N−1)}. The complementary minor identity of Jacobi gives |det D|=|det L| times the absolute determinant of the flag principal block of L⁻¹.

The matrix A⁻ᵀ equals (A−J/(q+1))/q. The flag principal block of L⁻¹ is therefore

    [q²(I+S+T) − q(ST+TS) + STS] / [q²(q+1)²].

The three terms correspond to the cases where both, one, or neither of the cross-incidences hold. The same flag and two flags differing in just their line or point give the first case. Exactly one cross-incidence gives a unique length-two walk of one of the two switch orders. On the orthogonal complement to all point-only and line-only flag functions, both switches are −I, so the inverse block has eigenvalue −1/q².

The span of point-only and line-only flag functions has dimension 2N−1 because the incidence graph is connected. On constants both switches equal q. For any zero-mean point vector a define flag functions e(p,l)=a_p and f(p,l)=(Aᵀa)_l. In their ordered basis the two switches act by

    S = [[q,q],[0,−1]],    T = [[−1,0],[1,q]].

This follows by summing over the lines at p or the points at l and using AAᵀa=qa. As Aᵀ maps zero-mean point vectors bijectively to zero-mean line vectors, these pairs span all the nonconstant point and line functions. Substituting the two matrices gives q²(q+1)I in the numerator, also its value on constants. Thus the inverse block has eigenvalue 1/(q+1) on 2N−1 dimensions and −1/q² on the remaining N(q+1)−2N+1=q³ dimensions. The complementary minor has absolute determinant (q+1)q^{N(N−1)−2q³}. Multiplication by the flag determinant proves the claim.

In particular either mixed cut has rank N² over the reals or any field whose characteristic divides neither q nor q+1. The point-pair versus line-pair cut has rank binom(N,2) as in the companion note; its ordered version duplicates the pair rows and columns and adds zero diagonal slots. Any set-multilinear algebraic branching program that reads the four variable groups once in any one fixed order thus needs width at least binom(N,2) at the middle cut. For orders with mixed first two groups this increases to N². This statement is about the four-group polarized component, a tensor-valued consequence of the original promise.
