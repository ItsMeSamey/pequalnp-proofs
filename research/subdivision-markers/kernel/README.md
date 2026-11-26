# Matching kernel and affine boxes

Run `python test_kernel.py` from this directory (Python 3.10+). Coordinates are nonnegative integers encoding binary vectors. `solve(pairs,h)` returns a list of labels 0,1,2, or None. `kernelize` separately returns the compact instance and a witness-lifting function. Its polynomial runtime includes the bit lengths of the input vectors.

## Matroid intersection certificate

The search starts at both elements of unused groups. From an outside element in the linear span it visits selected elements in its unique basis representation. An outside element independent of the current selection terminates the search. From a selected element it visits its mate. Along a shortest successful path write the outside elements in order as x0,...,xt, with displaced elements y1,...,yt. For every i<t, xi has a nonzero coefficient at y(i+1) and zero coefficients at later displaced elements, or the path could be shortened. This triangular coefficient matrix is nonsingular. Replacing the displaced columns by x0,...,x(t−1) preserves independence and span, and adding xt increases rank. Group feasibility follows from the alternating path and its unused starting group.

If search fails, the reachable elements are exactly the union of complete groups J. Every reachable unselected column lies in the span of reachable selected columns by the search rule. Therefore these selected columns form a basis of the columns in J. Outside J each group contributes one selected column, giving the tight rank upper bound rank(J)+n−|J|. This proves maximal cardinality independently of any library. If the selected columns span the whole column space, they realize every consistent target. Otherwise the non-J groups project to fewer groups than the quotient rank. The two elimination steps implement quotient coordinates and witness lifting.

## Deterministic time bound

For a block of b labels, each excluded word defines a box of size 2^b by forbidding its symbol at every position. Each ternary word belongs to 2^b boxes. Greedily choosing the box that covers the most uncovered words leaves at most 3^b exp(−t(2/3)^b) words after t steps. Thus at most floor(b ln(3) (3/2)^b)+1 boxes suffice. In one global box, choosing between two allowed vectors at each position is a binary linear system. Elimination gives either two-choice selections meeting the target or an inconsistency certificate for the box.

With m residual groups, take blocks of size ceil(m/16), using at most 16 blocks. The product contains at most O((m+1)^16 (3/2)^m) boxes. Explicit mask construction, including arbitrary-precision costs, and greedy cover selection take O*(81^ceil(m/16)) time and O*(9^ceil(m/16)) space. For example, the greedy loop has at most 3^b iterations, each scanning 3^b masks of length 3^b, and building masks by summing single-bit integers costs at most O*(27^b). Since 81^(1/16)<3/2, the decision and witness bound is O*((3/2)^m) after preprocessing, hence O*((3/2)^k) for row rank k. Here O* suppresses polynomial input factors. The polynomial degree and the implicit constants make this an asymptotic result.

Alternatively use block size max(1,floor(log2(m+1))) to obtain polynomial space and (3/2)^(m+o(m)) time: the logarithmic overhead from the per-block factor is O(m log log m/log m). Both guarantees concern this specific parameterized problem.

The deterministic test suite checks 1,001 exhaustive group multisets (up to four pairs, two-dimensional vectors) and 500 seeded instances. Tests independently verify the intersection upper bound, solver results against direct enumeration, and lifts of every feasible quotient word tested. They verify the box cover directly through block size four.
