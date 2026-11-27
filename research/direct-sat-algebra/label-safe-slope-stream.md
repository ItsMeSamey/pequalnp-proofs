# Polynomial-space extraction of the label coefficient

Lift the h-label square-zero computation in label-safe-slope.md to an ordinary polynomial circuit. Retain all additions and multiplications, including multiplication by the pivot itself. Bound every carry propagation by h+1 steps: its minimum total degree increases each time. The circuit reduces to the correct square-zero answer modulo squared labels and so has its exact top squarefree coefficient.

For each subset S replace its labels by X and the rest by zero. In K[X]/(X^(h+1)) evaluate the lift, extract its coefficient of X^h and sum over S. A monomial with support U appears 2^(h−|U|) times; only monomials supported on every label survive. Degree h forces each exponent to be one. Thus univariate arithmetic need not satisfy the original square-zero identities. The pivot is used as a multiplier even if it would not be its own inverse in the univariate ring. Direct Boolean evaluation without filtering homogeneous degree would be incorrect.

Each specialization costs polynomial bit time and space. One prefix costs O*(2^h) time, and the default search uses O*(2^(d/2)) bit time and polynomial space, including original binary rank replay. For d=1 use 1+A(1).

Attribution: Dickson matrix background https://arxiv.org/abs/1211.5475 ; ranked subset convolution in the dense solver https://arxiv.org/abs/cs/0611101 ; established substitution-sieving techniques for multilinear monomials https://arxiv.org/abs/1209.1082 . No priority claim is made for these components.
