# A third prescribed vertex in a subcubic graph

Given a simple graph G of maximum degree three, an edge st, and a vertex v, a deterministic O(|V|+|E|) algorithm decides whether some induced subgraph containing s,t,v has all degrees even, and produces such a vertex set. This permits any simple graph, including nonbipartite ones. The marker here is a prescribed vertex.

A selected vertex has degree zero or two. Each nontrivial component of the selected subgraph is therefore an induced cycle, with no edges between different components. The edge st lies on one such cycle C. If v is outside C, taking only C and v gives a witness in which v is isolated.

If v equals a root, test reachability from s to t after deleting edge st; a shortest return path gives C. If v is adjacent to s, it is on C, and the marked segment is t,s,v. Delete s and its neighbors other than t,v; a shortest remaining t-to-v path supplies the required cycle exactly when one exists. Exchange s and t for the other adjacency case.

Otherwise put H=G−st. Compute the components of H−N[v]. When s,t lie in the same component, a shortest path between them and the root edge yield an induced cycle anticomplete to v. Add v. If s,t are in different components S,T, any remaining witness is a cycle C through v. Enumerate the ordered neighbors a,b that precede and follow v on the return path from s to t. Require a≠b and a,b nonadjacent. All other vertices of C avoid N[v]. Hence the initial arm s to a has its internal vertices in S, and the terminal arm b to t has its internal vertices in T. Reject the pair if the first arm cannot be found in H[(S∪{a})−N(b)], or the second in H[(T∪{b})−N(a)]. Otherwise shortest arms join via a,v,b and edge st to make the desired cycle. The two components forbid any chord between their vertices in H; the deletions exclude chords from either attachment vertex to the opposite arm. There are at most six ordered pairs. Breadth-first search can retain predecessors in every case.

The checker exhaustively compares decisions with all feasible masks on every labelled subcubic graph through five vertices, including every root edge and every marker vertex (17,856 queries total).
