# Boundary rank for a prescribed number of orbits

Let M(b,k) have rows and columns indexed by permutations of b labels and entry one if their relative permutation has exactly k cycles (fixed points included), zero otherwise. For b≥1 and 1≤k≤b, over characteristic zero,

    log rank M(b,k) = 2b log min(k,√b) + O(b),

uniformly in both parameters. This gives an interface bound even for a single specified interior coefficient, in contrast to extracting all coefficients together.

In the regular representation, the generating matrix is convolution by the central element summing every permutation with weight z to its number of cycles. On a partition λ of b its scalar is the product of z+column−row over all cells of λ. This is the Jucys–Murphy content identity. The λ-block has dimension (f^λ)², where f^λ is the number of standard tableaux of shape λ. Thus the exact rank is the sum of (f^λ)² over λ whose content product has nonzero coefficient of z^k. [Content eigenvalues and class products](https://doi.org/10.1090/noti2474)

A contributing partition has Durfee square of side at most k. Its standard tableaux have at most (2k)^b possibilities: insert labels in increasing order, specifying the row for a cell in the first k rows and otherwise the column among the first k columns. Each instruction identifies its new cell. There are at most 2^b partitions and the entire matrix has b! rows. These bounds give the upper estimate.

If k≤√b take k nearly equal rows. The Durfee side is k, so the degree-k coefficient is the nonzero lowest coefficient. Each hook is at most 3b/k. The hook-length formula yields f^λ≥(k/(3e))^b.

For b=d²+1 and k≥d use the d-by-d square with its first row extended by one cell. Its content product is

    (z+d) z^d ∏_{j=1}^{d−1}(z²−j²)^{d−j}.

Every degree from d through b occurs. The middle product has alternating nonzero coefficients in all its even degrees, and the two terms of the linear factor shift them into opposite parities. Every hook is at most 2d, giving rank at least (b!/(2d)^b)². For general b≥2 let d=floor√(b−1) and b₀=d²+1. The b₀-strand matrices occur as submatrices on b strands with the target cycle count shifted by any t between zero and b−b₀. Leave t added labels fixed on both sides. Extend the two permutations by identity on the remaining added labels and splice those labels into one cycle on the first side by left-multiplying by a cycle through label one and those new labels. After forming the relative permutation this inserts a chain into an existing cycle without changing its count. The two index maps are injective. For k≥√b choose the shift so d≤k−t≤b₀. Since b−b₀=O(√b), the log-rank loss versus b log b is O(b). The case b=1 follows directly.

Any fixed bipartition with h Boolean interface wires carrying an unrestricted sum of products gives rank at most 2^h. Hence for k→∞ even an arbitrary signed interface at this boundary requires superlinear-in-b many bits. This obstructs compression across the specified cut, not algorithms using another representation. For the narrower model of ordinary permutation action on b tensor factors of dimension a<b, the antisymmetrizer vanishes, whereas the signed sum of exact-k indicator values is (−1)^{b−k} times the positive number of permutations with k cycles. No linear functional on that ordinary action represents this indicator. The antisymmetrizer argument alone allows no extra external sign twist.

[Finite rank and palette checker](orbit_profile_check.py)
