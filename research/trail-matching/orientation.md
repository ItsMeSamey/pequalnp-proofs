# Polynomial recognition over all diagonal orientations

Each guard i can be oriented in either direction between masks M_i and M_i△{i}; reversing requires toggling b_i since x_i²=x_i. This preserves the Boolean guard relation. We decide whether ANY orientation and trail decomposition has each pivot occurring in at most one initial mask. The algorithm also works with specified coordinate capacities in place of one.

For given orientations, maximally pair incoming and outgoing edges at each vertex v. The least number of starts there is s_v=max(0,outdeg(v)−indeg(v)). As the mask graph is a forest, pairings do not leave directed closed walks. Let K_C be the sum of s_v in tree C. For coordinate i, the unique edge flipping it lies in one tree T(i). On every other tree C the bit is a constant a_Ci; inside T(i), the vertices with bit i equal to one form one side of edge i. Its load is

    sum_{C != T(i)} a_Ci K_C + sum_{v on the one-side of i} s_v.

Fix external counts k_C. The residual capacity in the tree containing i is the specified maximum minus that first term with k_C substituted. A negative residual makes that tree infeasible. Let F_T(k) be the minimum total starts realizable on T with these residual side capacities, or infinity if none works. It depends only on counts of other trees and is coordinatewise nondecreasing.

To compute F_T try K=0,...,|E(T)|. Root the tree. For each vertex and orientation of its parent edge store achievable subtree start totals up to K. Combine children by knapsack with states (sum of child totals, number of outgoing child edges). Add the parent-edge direction to obtain the outdegree of v, then add max(0,2*outdegree−degree(v)) to obtain its subtree total. Check each child's edge capacity using the child total when that subtree is its one-side, or K minus that total otherwise. Require the root to attain exactly K. Backpointers recover an orientation for the first feasible K. The loops and table ranges are polynomial in the tree size, even for unbounded degree.

Start k at zero and repeatedly replace it by F(k). If an entry is infinite, no global admissible orientation exists: for any globally feasible totals k*, F(k*)<=k*, so monotonicity gives k<=k* throughout. Starting from zero gives a nondecreasing sequence. Finite totals across all trees sum to at most n, the number of guard rows. Thus at most n strict finite increases precede stabilization or failure. At a fixed point every local minimizing orientation attains its prescribed total under exactly the external loads of the other chosen orientations. Their union satisfies every capacity. Maximal pairings now produce an admissible decomposition. Arbitrary feasible pairings could have been replaced by maximal ones, so the criterion is exact for the trail method.

This covers disconnected trees sharing coordinates across many masks and requires no supplied trail orientation. It does not characterize other matching encodings.
