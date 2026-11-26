# Deterministic image membership for Boolean quadratics in finite abelian groups

Let G be a finite abelian group, given in invariant-factor coordinates, with order g and exponent m. For coefficients in G and Boolean variables, consider

    Q(x) = c + Σ_i b_i x_i + Σ_{i<j} w_ij x_i x_j.

Membership of a prescribed y in the image of Q, with witness recovery, is decidable in deterministic time f(g) poly(n) for a computable f. This covers cut-only markers with arbitrary G-valued edge weights because the indicator of an edge crossing a shore is x_i+x_j−2x_ix_j. Fixing, identifying or complementing individual bits preserves the quadratic form under substitution. A bounded number of binary affine equations can be imposed by adjoining their values as extra binary output coordinates. The result concerns image membership. We have not derived an FPT algorithm here for a simultaneously selected even subgraph disjoint from the cut.

The use of Boolean rank, diagonal rigidity and high-rank equidistribution for modular Boolean quadratics predates this argument. See [Holden Lee, Theorems 3.1 and 4.1](https://arxiv.org/abs/1509.08896). We give an algorithmic finite-group argument with explicit certificates using subgroup sizes, including nonunit coefficients.

## A scalar test at any threshold

For a character χ of G, identify its values with exponents modulo m by fixing a primitive mth root of unity. Denote the resulting symmetric matrix of pair coefficients by A, with diagonal arbitrary. Treat the constant and linear terms separately. Build disjoint lists I and J of equal length, initially empty. Write H for the image of A[I,J] over Z/m. Adjoin two different unused indices i,j to I,J, respectively, whenever this strictly increases the image size. Test candidates in a fixed order independent of the threshold. Enlarging the block preserves the old image under projection, so its image size grows by an integer factor of at least two and at most m². Indeed adding a column multiplies the image size by the index contributed by one element, at most m, and adding a row has a projection kernel inside Z/m. Stop on reaching |H|≥2^R, or if no pair works. A threshold run uses at most R growth steps. Enumeration of the image costs m^{O(R)} poly(n).

**If growth stops early**, let K be the unused indices. For |K|≤1 simply record their bits together with the bits in I and J. Otherwise, adding only row i in K or column j in K does not increase image size, since one can then add a different unused index on the opposite side. Hence v_j=A[I,j] belongs to H, and row i determines a homomorphism g_i:H→Z/m, with g_i(A[I,J]z)=A[i,J]z. For distinct i,j in K, the joint extension still has image size |H|. Projection to I induces an isomorphism onto H, whose extra coordinate is already g_i on the old columns, so A[i,j]=g_i(v_j). The pair interactions outside the bounded exceptional coordinates are thus determined solely by the two types (A[i,J],A[I,i]) and (A[j,J],A[I,j]); no invertible pivot or prime field is required.

**If growth reaches the threshold**, its nontrivial character phase has small bias uniformly over all constant and linear terms and all variables outside I∪J. More precisely, for every modulus m≥2 and tolerance η>0 there is an effective R=R(m,η) such that the absolute bias is less than η. Condition on the outside variables. For B=A[I,J], with x and u independent uniform Boolean vectors on I and J, the remaining phase is α(x)β(u)exp(2πi xᵀBu/m), where the factors have modulus one. Cauchy–Schwarz on u and independence of the u coordinates yield

    |bias|² ≤ E_{x,x′} ρ^{wt(Bᵀ(x−x′))},     ρ=cos(π/m).

Here x′ is an independent copy, and each nonzero coordinate of Bᵀ(x−x′) contributes an absolute factor at most ρ. The images of B and Bᵀ have equal size. Indeed the kernel of Bᵀ is the annihilator of im B under the perfect pairing on (Z/m)^I. Greedily choose generator columns of Bᵀ, adding a column whenever it is outside the subgroup already obtained. Each enlarges that subgroup by at most m, so there are at least R/log₂(m) selected columns. Their Boolean subset sums are distinct, since the last differing column of any two subsets would otherwise be in the subgroup of its predecessors. Condition on x′ and on all other x bits. The maximum atom of Bᵀ(x−x′) is at most 2^{−R/log₂(m)}. Its dimension is at most R. For any positive integer k≤R the bias squared is therefore at most

    2^{−R/log₂(m)} Σ_{j=0}^{k−1} binom(R,j)(m−1)^j + ρ^k.

First choose k so that ρ^k<η²/2, then choose R sufficiently large that the first term is smaller than η²/2. These choices are effective using rational upper bounds, for instance ρ≤1−1/m² and log₂(m)≤m. For m=1 return the zero group answer directly.

## Joint feasibility

At a low threshold R, call L the characters whose growth stopped early, and take U to be the union of their pinned sets, including the possible last unused singleton. Thus |U|≤g(2R+1). For each i outside U its joint type records, for every χ in L, the linear coefficient, the row and column values defining g_i and v_i, and the interactions of i with all of U. There are at most

    T = m^{g(1+2R+g(2R+1))}

possible types. For fixed bits on U, each low scalar quadratic depends only on the counts of selected elements of each joint type modulo 2m. The contribution within a type is a constant times binom(count,2), periodic modulo m with period 2m. Between two types the contribution is a constant times the product of their counts. Enumerate the bits on U and the attainable residues of the counts, or directly choose representative counts between 0 and min(class size,2m−1). This determines whether all low equalities χ(Q)=χ(y) are feasible. Each attained joint count-residue and pinned-bit choice has probability at least

    d(R) = 2^{−g(2R+1)−(2m−1)T}

under uniform Boolean input. Within a class with fewer than 2m−1 bits, some assignment realizes each attainable count. With at least 2m−1 bits, their first 2m−1 already realize every residue modulo 2m with probability at least 2^{−(2m−1)}. Convolution with the remaining bits preserves this lower bound. Multiply over distinct types and pins.

Use thresholds R₀=1 and R_{j+1}>R_j large enough that every character reaching the new threshold has bias less than d(R_j)/(2g). The early-stopping characters increase monotonically. After at most g increases either all characters stop early, or two consecutive low sets coincide. In the former case check their equalities directly. In the latter let L be the common set and H its generated subgroup in the character group. If the low equalities are impossible, y is impossible. Otherwise Fourier orthogonality gives

    g Pr[Q=y] = |H| Pr[∀χ∈L, χ(Q)=χ(y)] + Σ_{χ outside H} E[χ(Q−y)].

The first term is at least d(R_j); every summand in the second term has absolute value less than d(R_j)/(2g), by stability of L and the high test at R_{j+1}. Thus Q=y has positive probability. This is an exact deterministic decision using only low-feasibility and subgroup-size computations. Repeatedly pin one bit and decide the residual instance to extract a witness. Every threshold, number of characters, cost of computing images and enumeration of type counts is bounded by a computable function of g. Input access and the number of candidate pairs tested per step are polynomial in n with parameter-independent exponent.

The finite checker covers 540 seeded modular forms including nonprime powers and nine count-periodicity families. It verifies low subgroup reconstruction, transpose image cardinality, the growth-factor bound and equal values on equal signatures. It does not implement the large theoretical threshold ladder.
