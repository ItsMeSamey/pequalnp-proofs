# Exact counting with a perfect matching of cubic monomials

There is a deterministic one-query polynomial-time metric reduction from #CircuitSAT to the exact gap Z(F)=∑_x(−1)^{F(x)} of an explicit squarefree binary cubic F. Every variable occurs in exactly one cubic term, the cubic terms are disjoint, and the simple graph of quadratic terms has maximum degree at most four. The Boolean DAG uses O(q) binary gates for q variables. The single instance has q=O(N²), where N is the original number of declared input bits plus binary gates plus one. A construction of size O(N) recovers the original count modulo three, including exact decision under the zero-or-one promise. The output polynomial's own Boolean satisfiability is a different task. Exact #ones and the gap interconvert via Z(F)=2^q−2 #ones(F).

General cubic-gap hardness and hardness with at most three incident terms per variable are established by Montanaro, Proposition 7. Here every input lies in the matching of cubic terms. We give the reduction and its decoding explicitly. [Montanaro, Quantum circuits and low-degree polynomials over F₂](https://arxiv.org/abs/1607.08473)

## Prepare disjoint cubic terms and spare bits

Introduce a value z_g for each binary gate and write its defining equation z_g+g(inputs)=0 as a degree-two Boolean polynomial. Add the equation output=1. With b equations, introduce a Fourier bit for each and sum the products with their equations modulo two to form P. Summing (−1)^P over all variables gives 2^b times the original #CircuitSAT answer: raw inputs have unique consistent gate values, and the output equation selects acceptance. P has O(N) variables and terms. Use its combined squarefree ANF.

Replace each variable's occurrences in different monomials by separate ports; a variable used nowhere keeps an unused port. Tie consecutive ports u_j,u_{j+1} for the same variable by adding λ_j(u_j+u_{j+1}) with a fresh multiplier per link. Let e count the links. The new phase G on n=O(N) bits has Z(G)=2^{b+e} #CircuitSAT. Every cubic term is on three distinct private ports. Each port occurs in at most one original monomial and two multiplier links. Let T be the k spare variables outside the cubic terms, including all multipliers. The case k=0 needs no further reduction.

## Unary chains and one-query decoding

For every spare logical bit u_1 install a chain of length L. For i=1,…,L add the cubic u_i a_i b_i, with fresh a_i,b_i; all u_i except u_1 are also fresh. Add u_i u_{i+1} on consecutive positions. Conditional on u_1, summing all other chain bits gives the signed weights

2^L(A_L,B_L), with (A_1,B_1)=(2,1) and (A_{j+1},B_{j+1})=(2(A_j+B_j),A_j−B_j).

Summing a,b for one fixed logical gives (4,2). One quadratic coupling changes two suffix sums into their sum and difference before those local weights apply. Inductively A_j>B_j>0, A_j is even, B_j odd, and gcd(A_j,B_j)=1: a common odd divisor of A+B and A−B divides both A and B. Also 2^L≤A_L≤4^L. All variables now lie in disjoint cubic triples. An old spare port can see one inherited quadratic term, two links, and one chain neighbor. Other vertices have no higher quadratic degree.

Set L=n+2, A=A_L, B=B_L. Let C_j=∑_{x:wt(x_T)=j}(−1)^{G(x)}. Then |C_j|≤2^n<A/2. The returned gap divided by 2^{Lk} is the signed integer

D_k=∑_{j=0}^k C_j A^{k−j}B^j.

Modulo A only C_k B^k remains. Since B is invertible modulo A, C_k is uniquely its decoded balanced residue; the strict coefficient bound avoids a tie. Replace D_k by (D_k−C_k B^k)/A and repeat in descending order to recover all C_j. Their sum divided by 2^{b+e} is the desired original count. There are O(n²) variables and terms and the integer weights and all intermediate decoding operations have polynomial bit lengths. The procedure also covers negative returned integers. Each variable belongs to one cubic term, which costs two AND gates, and the sparse quadratic and affine terms add only O(q) gates.

For a modulo-three answer use L=3, so (A_3,B_3)=(14,5)≡(2,2) modulo three. On either logical value the full chain weight 8A_3 or 8B_3 equals one modulo three. Therefore Z(F)≡Z(G)≡2^{b+e} #CircuitSAT modulo three, and 2 is invertible there. This instance has O(N) variables and gates. In particular the zero-or-one promise on the original count admits a linear-size deterministic reduction to the gap-residue decision problem. This leaves open deterministic isolation of a single witness on arbitrary circuits.

## Why testing for a nonzero gap cannot replace decoding

For any matching of m cubic terms covering all 3m inputs, with arbitrary quadratic and affine terms added, Z(F) is 2^m times an odd integer. Ignore a constant, which only changes the sign. Expand the sign into factors (1−2M) for its distinct nonconstant monomials. A choice of h monomials covering v coordinates contributes (−2)^h 2^{3m−v}. For h<m use v≤3h, for h>m use v≤3m; in both cases divisibility is by at least 2^{m+1}. At h=m only a cover of all coordinates contributes modulo 2^{m+1}. Such a cover must consist exactly of the disjoint cubic terms, so it contributes ±2^m modulo 2^{m+1}. Thus every instance in this class has nonzero signed sum. The metric reduction uses its numerical value. Polynomial-size reductions in these statements give no lower bound on exact runtime. For a single explicit cubic polynomial, existence of an input with F=1 is decided by testing whether its Boolean ANF is nonzero.

The bounded checker cubic_unary_radix_check.py enumerates chains of lengths one through three, a two-chain example and a two-gate Fourier encoding, and tests balanced-residue recovery on 84 small random phases including negative coefficient examples. The variable-splitting proof and all-size complexity claim are separate from the finite tests.
