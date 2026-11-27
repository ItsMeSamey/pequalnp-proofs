# Arbitrary-arity incidence projection

Make a bipartite multigraph on maximal signed comparison paths and OR clauses, using one incidence per physical occurrence. Give each otherwise unanchored closed path one retained anchor. Good paths have endpoint xor equal to their request xor. Any extension reserves distinct incidences for one failure per bad path and one success per clause. A tree has too few incidences unless some path is good. Emit one OR of all its good-path tests; an isolated empty clause rejects. Cyclic components emit nothing.

Root each tree at a good path. For a cyclic component take a spanning tree and root it at one endpoint of an extra incidence. Assign that incidence to the cyclic root, and each parent incidence to its child. Fail just the incidences assigned to bad paths. Each clause keeps its own successful incidence. Integrate signs along each path and undo copy offsets. This proves existential projection and conditional original witness recovery. Counts can change. Parallel incidences and loops need distinct IDs.

If every clause has arity at least two, every leaf of a tree component represents a singleton path. When every path has length at least two all assignments extend. Unary clauses invalidate this corollary. With all paths singleton the whole starting constraint system can survive.

For N indexed vertices, clauses and occurrences, construction and lifting use O(N) indexed operations and words on a RAM with O(log(N+2))-bit words. Index-manipulation bit work on a random-access bit-cost model is O(N log(N+2)); arbitrarily large or sparse external names and mapping lookup costs must be charged separately. Solving the resulting clauses is additional.
