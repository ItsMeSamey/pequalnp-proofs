# Two weaker promises for projective-plane incidence

Use the prime-field plane of order p, with N = p²+p+1. Index both point addresses and line coefficient vectors by the normalized triples (a,b,1), (a,1,0), (1,0,0). Incidence means the dot product is zero modulo p. Gate counts below are for binary monotone AND and OR with free fanout. Hardwired constants may be propagated.

## Total input weight at most two

There is an O(N)-gate circuit exact on every assignment selecting at most two input bits in total. On each side put the indexed inputs at the leaves of a complete binary tree padded with zero leaves to the next power of two. Compute all subtree ORs. For each address position, OR all left children at the corresponding depth and separately OR all right children. With exactly one selected input, the two results encode the complement and value of that address bit. Each child signal occurs at only one depth, so producing all address rails and the root presence signal costs O(N) gates.

For index i below p² the coordinates are (floor(i/p), i mod p, 1). For the next p indices they are (i−p²,1,0), followed by (1,0,0). A Boolean circuit of size polynomial in log p decodes both indices and tests the dot product. Schoolbook multiplication takes polynomially many bit operations, and long division scans O(log p) bits with comparison, subtraction and selection at each step. Simulate each Boolean wire by positive and negative rails. For AND use AND on positive and OR on negative rails. For OR interchange the operations. NOT swaps rails. This uses at most two monotone gates per Boolean gate and computes complementary answers on complementary inputs.

Conjoin the positive answer with both root presence signals. If a side is empty, the output vanishes. Otherwise total weight at most two forces both addresses to be valid singletons, so the output is the required incidence bit. The circuit costs O(N + polylog p) = O(N). All restrictions that set variables to zero preserve this promise on surviving variables. Along sufficiently large primes, even tagging every gate fits the strict Np/100 budget.

## Arbitrary point masks and at most k selected lines

For 1 ≤ k ≤ N first build a monotone singleton-line tester F(X,Y). Compute the line address rails and presence as above. For each point u hardwire its triple, evaluate its incidence with the decoded line using dual rails, and conjoin the result with X_u. OR these terms and conjoin line presence. This costs O(N polylog p), rejects empty line masks, and computes the exact edge predicate for singleton line masks with arbitrary X.

Set B = 2k². A random coloring of lines into B colors collides on any fixed k-set with probability at most binom(k,2)/B ≤ 1/4. For T = ceil(k log₂ N)+1 independent colorings the probability that some k-set has a collision in every coloring is at most N^k (1/4)^T < 1. Fix a successful family. Every smaller set extends to a k-set, so some coloring is injective there too.

For each coloring h take the OR over its B buckets of F(X,Y restricted to that bucket), implementing restrictions by hardwired zeros. AND these ORs across h. A selected incident pair makes the bucket containing its line accept for every h by monotonicity. If no pair exists and |Y| ≤ k, a coloring injective on Y yields only empty or singleton buckets, all of which reject. The nonuniform size bound is O(T B N polylog p) = O(N k³ polylog p), absorbing log N into the last factor. For fixed 0 < ε < 1/3 and k ≤ p^(1/3−ε), the bound is o(Np) and all gates can eventually be tagged. The original problem requires correctness through k = p and remains open.
