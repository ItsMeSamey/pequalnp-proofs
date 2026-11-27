# Fewer disjoint bases at each dimension

In the dimension-j step in ternary-vector-neutral-recursion.md one can use s=ceil(log₂(4j)) complete bases. For a character χ define w_i(χ) as the number of vectors in basis i with a nonzero pairing with χ. The product characteristic function for uniform independent cycle toggles has magnitude product_i 2^(−w_i(χ)). Hölder's inequality with s equal exponents gives
  sum_χ product_i 2^(−w_i(χ)) ≤ product_i (sum_χ 2^(−s w_i(χ)))^(1/s)
                               = (1+2·2^(−s))^j.
Every basis bijects the characters with ternary words of length j, proving the equality. By the bound on s this is at most (1+1/(2j))^j<2. Removing the trivial term leaves less than one; Fourier inversion ensures strictly positive mass at each target. The exact subset-sum DP recovers a witness from the cycles. This is the classical additive-bases estimate of Alon, Linial and Meshulam, https://doi.org/10.1016/0097-3165(91)90045-I.

Only O(j log(2j)) short cycles are removed before either successful synthesis or scalar projection. Optimizing the deletion window gives x=O(sqrt(nF(n)·j log(2j))) portals, with F(n)=max(1,log(2n)loglog(4n)). If the formal choice of L is below one, choosing all n portals meets this last bound. The recursion therefore has logarithmic running time
  O(sqrt(nF(n)) log(2n) · b^(3/2) sqrt(log(2b)) + b² + log(input length)).
The bound employs endpoint-batched enumeration of parallel labels. It is subexponential in n apart from polynomial input factors if b³ log(2b)=o(n/(F(n)log²(2n))); b=O(log n) is one particular regime. No conjectured constant number of additive bases is needed.

The mathematical algorithm is deterministic. Implementations and checker reports must specify whether they use the scalar, the vector, or the sharpened short-cycle threshold.
