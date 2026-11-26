# A stationary chart objective need not be additive on basis incidence

Use rank-four binary column masks (13,4,2,5,1,8,14,7,3), with elements numbered 0 through 8, s=0, t=1. The objective is one precisely when cycle C contains element 6. The complete list of nonempty anchored fibers at fixed cocycle is below. Masks encode subsets by element number. To check the table, enumerate the 16 dual vectors d and each subset C containing 1, retaining those with XOR of the chosen column masks zero and avoiding the support of (d·v_i)_i. Require d·v_0=1.

| d | cocycle mask | possible cycle masks | objective |
|---|---|---|---|
| 1 | 409 | 102 | 1 |
| 3 | 93 | 386 | 0 |
| 8 | 97 | 26,150,270,386 | 0 |
| 10 | 421 | 26 | 0 |

At fixed cycle the objective is automatically constant. Now take the following six compatible bases, written as strings of element numbers. Their chart values in order are shown below.

| basis | 0234 | 0256 | 0346 | 0347 | 0348 | 0578 |
|---|---|---|---|---|---|---|
| fundamental cycle of t (mask) | 26 | 102 | 26 | 26 | 26 | 386 |
| objective | 0 | 1 | 0 | 0 | 0 | 0 |

Each element occurs an even number of times across the six bases. Every affine function of their incidence vectors must therefore sum to zero, whereas the six objective bits sum to one. Thus single-element stationary objectives already exclude an additive common-basis weight formula, including after deleting the shared s or adding a constant.

## A conditional polynomial algorithm for one coordinate

Assume stationarity on individual fibers, let the objective be the indicator that e belongs to C, and suppose the supplied quotient M/s is represented by a graph H in which t and e are adjacent non-loop, nonparallel edges. Assume s is not a loop. Pick a linear functional a with a(v_s)=1 and assign sign bit a(v_i) to each edge of H. A graphic circuit Q lifts to a zero-sum original circuit iff its sign is zero: its lift sums to a multiple of s, determined by the sign. In that case its original span excludes s. Indeed no nonempty proper subset of Q has zero quotient sum, and the full subset has original sum zero. Thus some functional annihilates all of Q while taking one on s, giving the required disjoint cocycle. Conversely any anchored circuit Q disjoint from an anchored cocycle has span excluding s and remains a circuit in M/s. For any attainable objective take an anchored circuit inside the realizing cycle by circuit decomposition, retaining the same cocycle. Stationarity preserves its objective. Thus both target bits reduce exactly to signed graphic circuit tests.

For bit zero delete e and t, and ask for a simple path joining the ends of t with sign equal to the sign of t. For bit one delete the common endpoint of t,e and ask for a simple path between their other endpoints whose sign is the XOR of their signs. Reinsert the deleted edge or edges to obtain a balanced circuit. Both path problems are polynomial. In a connected graph follow the unique block-cut route between the endpoints (bridges count as blocks). A balanced block has a vertex potential giving its edge signs as potential differences, so its contribution is fixed. An unbalanced block on the route admits both signs between the distinct entry and exit vertices: take an unbalanced simple cycle and choose disjoint paths from those two vertices to distinct points of the cycle, allowing zero-length paths. Existence follows by vertex Menger in the two-connected block, including the case of a two-edge parallel cycle directly. Trim paths at first contact. The two arcs of the cycle give opposite signs. Blocks meet only at cut vertices, so their selected paths concatenate simply. Graph traversal, parity labeling, and a two-unit disjoint-path flow suffice constructively. A realizing cocycle follows by linear elimination. No graphic recognition is needed when the indexed representation is supplied.
