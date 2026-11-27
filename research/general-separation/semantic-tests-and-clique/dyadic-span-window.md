# A fixed dyadic test for exact real dictionary membership

Let A be any finite zero-one matrix with at most S columns, S≥1, and f a zero-one column on the same rows. Put B=ceil((S+1)log₂(S+1)/2)+1. Then

    f ∈ span_R(A)    iff    A c = 2^B f  (mod 2^(2B)), for some residue vector c.

The same B works for every candidate dictionary of that size and every target, with no restriction on the number of rows. Existence of an exact real representation with at most S admissible atoms is therefore equivalent to existence of this modular representation with the same term bound.

Let r=rank_R A. Every square minor of [A | f] of order at most S+1 has absolute value <2^B by Hadamard's inequality. If f is in the span, independent columns and rows give integer w and common positive denominator H<2^B with Aw=Hf by Cramer's rule. In the zero-rank case take w=0 and H=1. Write H=2^v h with h odd, so v<B. Set c=2^(B−v) h^(-1) w modulo 2^(2B).

If f is outside the span, some r+1 rows and some r independent columns J of A together with f give a nonzero (r+1)-minor D of [A_J | f]. The signed cofactors z for its last column satisfy zA_J=0 and zf=D on those rows. Each other column of A is in the real span of A_J, so zA=0 as an integer equality. Extend z by zeros on the other rows. Any modular solution forces 2^B to divide D, contradicting 0<|D|<2^B, including r=0 with the empty determinant.

If each row of A has at most d ones, one can instead use B=ceil((S+1)log₂(max(2,d+1))/2)+1 by applying Hadamard to the rows of the augmented minors. For fixed d an O(S)-bit shift and O(S)-bit precision above the shift suffice.

## Why both sides can need linearly many bits

Consider a test Ac=2^u f modulo 2^K, where 0≤u<K. The next systems have at most three nonzeros per row, at most four per column, and O(k) rows and columns. Each homogeneous equation is a row with f=0. One anchor row has f=1. Every coefficient within an individual equation is +1.

To impose y=2x use private columns b,t,s and four rows x+t=0, b+t=0, x+b+s=0, y+s=0. These enforce the relation over every commutative ring, and each feasible x,y extends uniquely. Consecutive gadgets share only chain variables. Index all rows in binary, with unused indices giving all-zero rows and target zero. Each column and the target then has an O(log(k+2))-leaf formula as the disjunction of at most four row-index equalities.

First use anchor a_0=1 over the reals (the modular anchor is a_0=2^u), and impose 2a_(i+1)=a_i for 0≤i<k. This is real-soluble with a_k=2^(−k). Modulo 2^K one needs 2^k a_k=2^u. If u<k and u<K this is impossible modulo 2^(u+1). Thus a shift u linear in dictionary size can be necessary.

Next use the same anchor, impose a_(i+1)=2a_i for 0≤i<k, and append a_k=0. There is no real solution. A modular solution exists whenever K−u≤k by taking a_i=2^(u+i) modulo 2^K with the private extensions. Thus linearly many bits above the shift can be necessary. Both obstructions match the order of the sparse-row upper bound. They concern a specified dictionary. Adding the singleton target as a feature gives an immediate real representation.

This elementary determinant argument gives a fixed-ring alternative to [prime avoidance](modular-weight-layer-obstruction.md). Treating the output as the top bit alone (K−u=1) admits false positives even for sparse dictionaries. Reading the target bit of a weighted sum requires carries. Neither arbitrary-real sparsity of a given lookup family nor ordinary P versus NP follows.
