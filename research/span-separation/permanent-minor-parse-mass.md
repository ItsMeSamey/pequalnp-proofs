# Absolute parse mass under random minor restrictions

Expand a signed syntactically row-multilinear circuit into parses and write w(f) for the total absolute weight of parses producing the column assignment f:[n]→[n]. The normalized absolute mass is C_n = Σ_f w(f)/n!. Retain k rows, chosen uniformly, and assign the other n−k rows to a uniformly random ordered list of distinct columns. Set the assigned entries to one and all remaining entries touching an assigned row or column to zero. The surviving permanent is a k by k permanent. Measure the inherited circuit without algebraic simplification. Vanishing parses contribute zero.

Let s(f) count rows whose assigned column has exactly one preimage under f. For fixed removed row set O, a parse survives exactly if all rows in O are singleton preimages and the random matching equals f on O. Thus its survival probability is binom(s(f),n−k)/binom(n,n−k) times k!/n!. This gives the exact expectation

    E C_k = (1/n!) Σ_f w(f) binom(s(f),n−k)/binom(n,n−k).

Every permutation has weight multiplier one, while every nonpermutation has s ≤ n−2 and multiplier at most k(k−1)/(n(n−1)). Writing D = Σ_{f bijective} w(f)/n!, this gives E C_k ≤ D + (C_n−D) k(k−1)/(n(n−1)). In particular averaging weakly improves C_n, strictly for k<n if some positive parse mass lies on nonpermutations. No strict improvement holds universally. For example two opposite copies of a scaled permanent can inflate D arbitrarily while leaving the output unchanged and preserving C_k = C_n for every restriction.

For a principal restriction pairing each removed row with its own column, define h(f) to count i with f(i)=i and f⁻¹(i)={i}. A uniform removed set then gives

    E C_k (principal) = (1/k!) Σ_f w(f) binom(h(f),n−k)/binom(n,n−k).

There is no universal monotonicity here. Add cancelling copies of K times the identity monomial to a monotone expanded permanent. Every principal restriction has C_k = 1 + 2|K|/k!, exceeding C_n when k! < n!. Randomizing by a uniform column relabeling before taking a principal restriction gives the random matching model instead.

Ryser's inclusion-exclusion formula is a signed sum over column sets S of products over rows of their sums on S. With these sums implemented directly, M_n = Σ_{j=0}^n binom(n,j) j^n. After any matching restriction a term vanishes unless S contains every removed column. Each surviving term reduces to the Ryser term for the intersection of S with the remaining columns, with exactly its k-dimensional sign. Therefore M_k = Σ_{j=0}^k binom(k,j) j^k deterministically for either restriction scheme (k≥1). Each permutation has exactly one supporting Ryser parse, so D=1. The normalized mass improves strictly with each dimension reduction from n≥2, but remains at least k^k/k! in the retained dimension, from its full-column term alone.
