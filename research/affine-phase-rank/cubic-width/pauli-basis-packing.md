# Different information sets certify positive postselection

For m independent commuting checks on a product of three-bit cubic sign states, form three X-component rows per physical block. Choose B layers, each using m distinct blocks and one vector in each block's row span, forming a basis of the m-dimensional generator dual. No block is reused. These bases need not coincide. Their maps T_i are invertible. Each one of T_i u certifies an active block in generator word u, so w(u)>=sum_i |T_i u|. Generalized Hölder yields

    sum_u 2^{-w(u)} <= product_i (sum_u 2^{-B|T_i u|})^(1/B) = (1+2^{-B})^m.

By the direct Pauli scalar formula in pauli-scalar-margin.md each global summand has modulus at most 2^{-w(u)}, and the identity has value one. If (1+2^{-B})^m<2, every sign syndrome is feasible. B=ceil(log2(2m)) suffices for m>=1. Local Z parts may be arbitrary subject to global commutation.

Construct a ground element for each physical block, each of its at most seven nonzero X-row-span vectors, and each layer. Use a partition matroid imposing at most one element per physical block and a direct sum of B represented matroids imposing layer-wise independence. A common independent set of size mB is equivalent to the required packing. Maximum-cardinality matroid intersection recognizes and finds it in polynomial time. Testing (2^B+1)^m<2^(mB+1) is polynomial in the explicit input when mB<=t, where t is the number of physical blocks. This sufficient test survives generator-basis changes. It provides neither an exact count nor a general witness for circuit SAT.
