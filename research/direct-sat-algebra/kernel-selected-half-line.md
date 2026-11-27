# Kernel-selected half-field line

For binary degree d=2a write Q=2^a and L=GF(Q). Center the supplied trace-self-adjoint A to an alternating operator B=A+M_c. If B is invertible return c. Otherwise compute any nonzero binary kernel vector x and set λ=x^(-2). An odd number of slopes in c+λL* make the original translate invertible.

Indeed sqrt(λ^(Q−1))=x/x^Q. In the paired-coset formula, multiply U_i=e_(i+a)+(x/x^Q)^(2^i)e_i by (x^Q)^(2^i) and sum from i=0 to a−1. This gives the Moore vector of x, in the kernel of the centered Dickson matrix D. Thus both D and U^t D U are singular, and the paired-coset identity gives one. Binary elimination chooses the line in polynomial time. Enumerating its members takes O*(2^(d/2)) time and polynomial space and ends with original-column rank verification.

If the omitted pole of the Möbius coset chart is an odd coset, the remaining affine predicate has even Hamming weight. The same holds for its complement since Q is even. Every Q-element binary scalar-translate determinant has odd weight because the nonzero kernel vectors across singular slopes partition the Q−1 nonzero vectors into odd-sized parts. Thus neither of those affine predicates equals a smaller scalar-translate determinant under any permutation of its parameters. The zero centered drift makes all cosets odd.

The good-slope predicate within the selected line itself has odd weight. Even there a uniform smaller drift representation fails. The exhaustive checker check_half_line_rank_indicator.py exhibits a GF64 selected line of weight five, whereas all 512 smaller GF8 drifts have weights one, three or seven. It also exhibits a GF256 selected line of weight nine outside the entire GF16 attainable weight set.
