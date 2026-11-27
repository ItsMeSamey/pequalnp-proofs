# Three required vertices localize to the median bag of the split tree

Given a connected finite simple graph and three distinct required vertices, seek a set containing them that induces even degree at every selected vertex. In a graph-labelled split tree the original vertices are leaves. The median node of the three pin leaves has one pin in each of three different incident branches. Every other branch is unpinned. Write B for the graph labelling the median node, with marker i for branch i. Within branch i let T_i consist of the leaves accessible to its marker. Two different branches i and j have all edges between T_i and T_j if ij belongs to B, and none otherwise. Each T_i is nonempty for a genuine split in a connected graph. A singleton leaf branch has that leaf as its frontier. [Gioan and Paul, accessibility graphs](https://arxiv.org/abs/0810.1823)

For a selected set let a_i be the parity of its intersection with T_i, and let b_i be the parity of outside neighbors seen by any frontier vertex. Then b_i is the sum modulo two of a_j over adjacent markers j. A selected vertex in branch i needs internal degree congruent to b_i if it is in T_i, and zero otherwise. Summing those required degrees gives a_i b_i=0. The remaining three possible states, in the order (a_i,b_i), are 00,10,01.

## The exact shore table

In an unpinned branch, the empty set supplies 00 and 01, and one frontier vertex supplies 10. For a branch with required vertex p, omit the branch index and put k=1[p in T] and U=T minus p.

* The singleton p supplies (k,0).
* State 01 exists if p is outside T, or if the component containing p meets U. In the latter case take a shortest path from p to U. Its endpoints alone require odd degree; its interior avoids T. Necessity when p is in T follows by summing degree parities in its selected component.
* For (1−k,0) an odd number of vertices of U must be selected. If some u in U is nonadjacent to p, select p and u. Otherwise U is contained in the neighborhood N(p). A solution then exists exactly when a component after deleting p meets both U and N(p) minus U. For necessity, after removing p from any witness, each remaining component contained an even number of its neighbors: those and only those vertices had their degree parity changed. An odd selected number from U forces one component to meet both classes. For sufficiency, take a shortest path between the two classes in the graph without p and close it through p. No interior vertex neighbors p, since it would belong to one endpoint class and shorten the path. The resulting induced cycle has exactly one vertex from U.

These witnesses are produced by adjacency-list, multisource breadth-first searches. The only possible nonempty tables and their exact representatives are as follows. All vertices described as frontier are joined to adjacent branches when the instance is reassembled.

| States | Representative |
|---|---|
| 10 | One required frontier vertex |
| 00,10 | Two nonadjacent frontier vertices, one required |
| 00,01 | One required nonfrontier vertex adjacent to one optional frontier vertex |
| 10,01 | Two adjacent frontier vertices, one required |
| 00,10,01 | One optional frontier vertex |

To see exhaustiveness, whenever state 01 fails, p is in T and its component contains no other frontier vertex. State 10 is available and 00 is available exactly when some other frontier vertex exists elsewhere. When 01 succeeds at least one of 00 and 10 is already supplied by the singleton.

## Construction, cost, and witness

Replacing all branches by their representatives produces an equivalent instance on at most |V(B)|+3 vertices with at most three pins. Alternatively retain the median-bag variables a and let b be B's binary adjacency matrix times a. Every marker imposes a_i b_i=0. The four proper tables above respectively add a_i=1, b_i=0, a_i=0, or a_i+b_i=1. A full table adds no constraint. Once a is known, union the stored branch witnesses for the corresponding (a_i,b_i). Each selected vertex then has the required internal and external degree parities. The reverse direction follows by restricting any original witness to each branch.

An existing split-tree algorithm takes O((n+m)α(n+m)) time. Given the tree and the original adjacency lists, label each vertex with its median branch and scan the graph edges. Endpoints of interbranch edges are exactly the frontiers. Tables and stored witnesses take O(n+m) additional time and space over the disjoint shores. Median-bag exhaustive evaluation costs O(2^|V(B)| poly(n+m)); this can be replaced by any exact algorithm for the represented instance. A prime median bag can have linear size. [Gioan et al., split tree construction](https://arxiv.org/abs/1104.3283)

The independent shore-table enumeration checked 162,741 labeled graph/frontier/pin triples on at most five vertices. The assembly test compares direct induced-subgraph enumeration to median-bag solving and lifts each affirmative result to verify every original selected degree. The assembly test uses supplied bag decompositions and does not implement split-tree recognition. [Shore check](check_single_pin_split.py) · [Assembly and witness check](check_split_median.py)
