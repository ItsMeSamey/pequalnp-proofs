# Rooted cocircuit triple evaluation is equivalent to binary basis evaluation modulo eight

For a binary r-row matrix A and distinct physical indices i,j,k let Q(A;i,j,k) over a binary field L count (r−1)-subsets F outside the triple such that F+i,F+j,F+k are all r-column bases, with weight product over F only. Put Q=0 at r=0. This is the cubic correction in the one-tag arbitrary-alternating-query formula. Fix L=F2^m and R=(Z/8)[X]/f where f is a monic lift of the binary irreducible polynomial defining L. The following deterministic polynomial-time oracle reductions hold uniformly in m, dimensions and bit representation. They concern polynomial evaluation on indexed weights, not existence.

## Mod-eight bases give Q

Let A0 be the columns outside the triple. For each of the seven nonempty subsets U of the marked sites take v_U equal to their binary column sum. Append it to A0 and contract it. Count zero if v_U=0 or rank[A0,v_U]<r, otherwise evaluate the resulting rank-(r−1) basis polynomial. Lift the original L weights arbitrarily to R, consistently across calls. For each F put a,b,c equal to its three binary extension determinants. The seven virtual probes give their nonempty XORs by multilinearity. The integer identity

    4abc = a+b+c − (a xor b) − (a xor c) − (b xor c) + (a xor b xor c)

gives four times the desired weighted sum after the same signed combination of ring evaluations. In the degree-<m representative each resulting coefficient is 0 or 4 in Z/8. Divide by four coefficientwise to recover L. This also efficiently evaluates a triple when all seven needed contracted matroids have supplied totally unimodular representations, via their ordinary ring Gram determinants.

## Q gives arbitrary mod-eight bases

Select a binary row basis of the original private matrix and take its literal zero-one integer lift A. Let d_S be its integer determinant for |S|=r. Compute G=det(A diag(w) A^T)=Σ d_S² ∏w over R by division-free determinant arithmetic. Odd d_S contributes one mod eight; multiples of four contribute zero. When d_S is twice an odd integer, its square contributes four in error. The true R answer equals G plus four times the L-weighted indicator of these supports; plus and minus coincide on multiples of four.

At binary corank ≥2 the integer Smith normal form implies 4 divides d_S. At binary corank one let x and y be the unique nonzero right and left kernel vectors. For any index j with x_j=1 replace that square matrix's column by the integer sum of the columns indexed by x, preserving its determinant. This new column is even; the other r−1 columns are a basis for the hyperplane y-perp. Dividing the even column by two gives

    d_S/2 mod 2 = y·((Σ_{j:x_j=1} A_j)/2 mod 2)
                = Σ_{j<k in S} x_j x_k (y·(A_j AND A_k)).

AND is coordinatewise in the fixed binary row basis. The second equality uses m/2 = binom(m,2) mod 2 for every even integer m, row by row.

Fix distinct j,k and put z=A_j AND A_k. For S containing j,k let b be det A_S mod two, and b_j,b_k the two determinants obtained by replacing j or k by z. At corank one b_j=x_j(y·z) and b_k=x_k(y·z). The required binary indicator contribution is (1+b)b_j b_k: at full rank it vanishes, at corank one it is the indicated pair term, and at larger corank both replacements are singular. In summing these correction terms discard all sites with zero residue weight; leave all original weights in G. Write I for the remaining original sites and use their nonzero residue weights. Skip j,k not in I.

The b_j b_k sum is a mixed Cauchy–Binet Gram determinant for the two replacement matrices. Force j,k into S by four weight-zero evaluations (binary inclusion–exclusion). If rank(A|I)<r the cubic b b_j b_k sum is zero, but the quadratic part may remain nonzero. Otherwise append the distinct new index z to A|I and form its binary matroid dual D, of rank rho=|I|+1−r. For each S containing j,k let F=I minus S, of size rho−1, outside j,k,z. The dual tests F+z,F+j,F+k being bases are exactly b,b_j,b_k by complementation. Its weighted cubic contribution is Q(D;j,k,z) times the product of all residue weights on I, using their inverses on nonroot sites in the Q instance. No factor is assigned to the new index z. This holds for parallel or zero z as well.

Sum the quadratic and cubic contributions for each pair in L, lift the total arbitrarily to R and add its fourfold multiple to G. This produces the basis polynomial with every original R weight, including nonunits. There are O(n²) Q calls and polynomial field/ring operations besides. Ranks r=0,1 can instead be handled directly.

## Scope for a single tag

The weighted full-support detecting polynomial in single-tag-cocircuit-correction.md also computes and is computed by Q. With g=e_k, Ω=e_i wedge e_j, the sole cubic term is D_ij D_ik D_jk. Add back the computable degree-at-most-two terms and set all three marked weights to one to obtain Q. The opposite reduction applies the full cocircuit-correction expansion. This concerns the precise weighted sum over r+2 full-rank supports, including their private coloops; singleton-tag decision itself is easy by dropping site k from the support of the actual relations. No decision hardness, fixed-modulus counting hardness, or impossibility of polynomial evaluation follows.
