# Uniform dimension bounds and the role of monotonicity

For the classical point–hyperplane incidence problem, let N = 1+q+…+q^d and k = 1+q+…+q^{d−1}, with d≥2 and q a prime power. The proof in projective-fixed-dimension.md (SHA-256 6f012837e49705d9906be2614f23d603f5bf20d4001cd41ffc84f270f1da0052) yields absolute constants in

    3N − 1 − Nσ/(k+σ) ≤ G ≤ 3N + O(N/q),     σ = q^((d−1)/2).

On the lower side this follows from the exact centered incidence estimate. Since (N−1)/q=k and k≥q^(d−1), the lower error is O(sqrt(qN)), hence O(N^(3/4)). On the upper side, the total number of absolute labels is at most 2(N−1)/q, by varying one chart coordinate. Both combined endpoint banks have at most 2(q+1)+4Σ_{j=2}^d q^{j−1} refined endpoints. This is O(N/q) with an absolute constant. With L=ceil(log₂N), d and the prime-field extension degree are at most L. Compare a coarse index with at most d+1 hardwired chart offsets, then unrank its varying coordinates by at most d base-q divisions. Expand field digits into polynomial-basis coefficients over the prime field and perform schoolbook multiplication and reduction. All decoder arithmetic uses poly(L) gates with an absolute exponent, and N/q≥sqrt(N). These bounds are uniform in the parameters. With canonical labels, naïve enumeration of a field representation and the bucket color classes also generates a circuit in polynomial time in N. Thus G/N tends to three whenever q tends to infinity and d may vary. At bounded q, this upper estimate alone does not give that limit. In characteristic two the absolute labels already form a projective hyperplane, of size k.

## Signed gates

The following circuit represents the same promise matrix of incidence A. For each row r let B_r be the OR of all its nonneighbor column flags. Form H as the OR of r AND NOT B_r, over all rows. Split the column flags into two nonempty parts, with ORs S and T. Output

    (H AND S) OR (H AND T) OR threshold₂(all column flags).

Each row has exactly one path to H and H has two live readers. Every row singleton makes H true. Nevertheless all row signatures are distinct. On the entire raw cube the computed function is monotone. No columns makes it false, one column tests that some active row is incident to it, and two or more columns make it true. All physical singleton inputs reject. This example refutes hot-interchangeability for signed circuits even under a globally monotone output and singleton rejection. It makes no claim about the minimum signed size.

At gate level AND(x,y) can itself be written as NOT(NOT x OR NOT y), so inferring the type of the common physical merge solely from rejected singleton and accepted joint inputs fails for signed gates. More generally a promise-only signed circuit can accept invalid one-sided singletons arbitrarily, and a single omitted flag per shore can be reconstructed by complementing the OR of the remaining flags. The spectral mixing argument remains a fact about the matrix, but establishing the requisite empty submatrix of cold flags requires a circuit theorem.

## Removing the promise

Any monotone circuit on the same full 2N-bit raw cube whose function agrees with incidence on the promise inherits the lower bound by restriction. The constructed upper circuit defines one monotone extension. It need not realize the existential-incidence function on arbitrary point and hyperplane sets. For distinct incident labels i,j, compare R={i,j}, L=∅ with R={i}, L={j}. Every folded label and all checked raw diagonal conjunctions agree, whereas the existential verdict differs. Even requiring nonempty sets does not repair this example in general: take k nonorthogonal to i and j and compare R={i,j}, L={k} with R={i,k}, L={j}.

A total specification that rejects every invalid one-hot input has no monotone realization as soon as some promised cell is positive and an extra flag can be raised. For a signed circuit of that total specification, adding a point or a hyperplane to a rejected cell may produce another rejected input, and the two-background first-merge sensitivity argument loses its starting premise. Finally, using binary names of points and hyperplanes changes the input representation: chart recovery and a finite-field dot test take only poly(log N) ordinary Boolean gates.
