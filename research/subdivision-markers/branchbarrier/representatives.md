# Tight lower bound for terminal-independent representative assignments

Use h disjoint blocks of q decisions. A decision may take value one exactly when the sum of earlier decisions in its block is even. Each guard is a single affine literal. The reachable points are exactly products of h alphabets consisting of the zero vector and q unit vectors. In each block the first one prevents every later one.

With k=h, for any tuple of unit vectors use h positive unit terminals requiring the selected coordinates. Exactly that prefix point satisfies these terminals. A prefix assignment pool that answers every such suffix by testing its retained assignments must contain all q^h tuples. This holds with qh prefix decisions and feasible guards of total explicit length O(hq²).

For general k≤h, the degree-at-most-k evaluation space restricted to reachable points has dimension

    sum_{j=0}^k binom(h,j) q^j.

Any monomial repeating two distinct coordinates in one block vanishes. The remaining multilinear monomials have at most one coordinate per block and are independent: for a linear relation evaluate successively at their own supports in increasing cardinality. Only the current coefficient and coefficients on proper subsets can contribute. Thus every evaluation-vector basis requires exactly the stated dimension. For k=h this equals (q+1)^h; nonlinear prefix representatives tested directly against suffixes still require q^h points.

The conclusion addresses explicit prefix assignments or the evaluation-space basis. A symbolic pool can represent this particular reachable set by its h independent factors, and a suffix-aware procedure can reconstruct its unique point directly.

The same lower bounds have a linear-length encoding with a dependency graph consisting of disjoint paths. In each block allow d_1 freely and guard d_j with d_(j−1) for j>1. Reachable strings are 1^a 0^(q−a), for 0≤a≤q. The invertible linear map y_j=d_j+d_(j+1), with d_(q+1)=0, sends these strings exactly to the earlier zero and unit alphabet. All suffix tests now have at most two variable occurrences. An invertible linear substitution and its inverse preserve the Boolean multilinear degree filtration, giving the same exact restricted evaluation rank. If positive unit terminals are required, the first construction applies.

In the path version even the zero symbol is isolated by one affine terminal d_1=0. Consequently h terminals (width at most two) can isolate every one of the (q+1)^h reachable points. This is the exact optimum for an explicit suffix-independent assignment pool.
