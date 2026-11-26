# The fifteen three-port parity signatures

Consider an arbitrary finite simple undirected graph with three distinguished vertices a,b,c. Fix the selected ports B. Require every selected internal vertex to have even degree in the induced subgraph. Its signature row records which sets of odd selected ports can occur. Temporarily remove edges whose endpoints are both ports. To restore owned port edges, XOR each row's parity with the odd-degree set of those edges induced by B.

Every row contains zero by selecting the ports alone. By the handshaking lemma each possible nonzero value is a pair of selected ports. Thus two sets specify the signature. Let P consist of pairs achievable when exactly that pair is selected, and Q consist of pairs achievable when all three are selected.

An internal component touches a port if it contains one of its neighbors. A pair uv lies in P if and only if some internal component touches both u and v. For sufficiency, a shortest path between u and v with interior in the component is induced. For necessity, some component of the selected subgraph contains both odd vertices, so a simple path joins them, internally avoiding the absent third port.

If P is proper, no internal component touches all three ports. With all ports selected, each component contributes either zero or the unique pair it touches, because all its internal selected degrees must be even. For such a touched pair the same shortest path realizes its contribution even when the third port is selected, as that port has no neighbor in this component. Different components are anticomplete and their contributions combine by symmetric difference. Consequently Q comprises exactly the nonzero vectors in the binary span of the incidence vectors of P. A replacement gadget uses one internal vertex adjacent to the two ports of each member of P. This requires at most two internal vertices.

When P contains all three pairs, there is no restriction on Q. The following four graphs, up to permutation of ports, realize all eight subsets. The letters x,y,z denote internal vertices. Every edge is listed.

| Q | Edges |
|---|---|
| empty | ax, bx, cx |
| ab only | ax, bx, cy, xy |
| ab and ac | ax, ay, bx, cy, xy |
| all pairs | ax, bx, ay, cy, bz, cz |

To verify the middle two rows with all three ports present, an internal subset is one of empty, x, y, xy. In the singleton-Q graph only empty and x satisfy internal evenness. In the two-pair graph empty, x, and y do so. In the last graph the three internal vertices are independent and each individually toggles its pair. In each of the four graphs, all port pairs can be linked by a shortest path avoiding the third port when that port is absent.

Hence exactly fifteen labeled-port signatures occur, each representable with at most three internal vertices and the owned port edges. The three-vertex bound is tight when P and Q both contain all pairs: the exhaustive checker covers every simple graph on the three named ports and up to two internal vertices, and none has this signature. The audit also enumerates every graph with three internal vertices, independently checking all chosen subsets for internal parity.

This statement concerns attainable boundary parities with unrestricted internal label. A weighted application can choose one original witness and its internal label separately for each achievable row entry. Labels of all other witnesses are the chosen label plus a correction from the same entry. This by itself does not establish closure of a restricted skeleton graph class under these replacements.
