# One unrestricted neighbor at a degree-four pinned middle

Suppose the three mandatory vertices induce the path a–h–c, and h has exactly four neighbors a,c,u,v. If u and v each have total degree at most three, the original induced-even problem has a deterministic linear-time algorithm with witness reconstruction. The degrees of a,c and of all other vertices are unrestricted.

First test a witness with h of selected degree two by looking for an a–c path after deleting h,u,v. If one exists, its shortest version plus h is an induced cycle. Conversely deleting h from such a witness leaves only a,c odd in the selected graph and forces them into the same component, with u,v absent.

After this test fails, a,c lie in distinct components X,Y of G minus h,u,v. A remaining witness must select all four neighbors of h. After h is removed from the witness, the odd vertices are exactly a,c,u,v. Each of u,v now has degree exactly one because it has odd degree and its remaining ambient degree is at most two. The selected vertices in X and in Y must each have an odd number of incident edges to {u,v}, by the parity of a cut. Consequently exactly one of u,v attaches to X and the other to Y, and uv is absent. Reject this branch if uv is an edge.

Test each assignment of ports to the components. Write U for the port assigned to X and V for the other. Find a path from a to U inside X plus U avoiding all neighbors of V. Seek a path from c to V inside Y plus V avoiding all neighbors of U. In any witness a,U are the only odd vertices on the X side with its assigned port, and c,V are the only odd pair on the Y side. Neither side uses a neighbor of the opposite port, whose unique selected incident edge is already on its own side. Conversely take shortest paths in these searches. Each path is induced. The components have no inter-edge, and the avoidance conditions exclude cross edges involving the ports. Adding h gives two cycles meeting only at h. There are a constant number of linear graph searches.

The next degree value on just one optional port represents every three-pin instance. From any graph with pins p,q,r toggle qr, add five vertices w,h,t,u,v and precisely these edges:

    wp  wh  ht  tv  hu  hv  ur  vp  vq

Pin w,h,t. Their path has degrees 2,4,2, and h's optional neighbors u,v have degrees 2,4. The selected w forces p. The selected t forces v. The selected h now forces u, which forces r. The four neighbors of v are h,t,p,q, so q is forced. Conversely appending all five new vertices to an old feasible support gives them degrees 2,4,2,2,4 respectively. Original p receives two new incidences, q and r one each; their toggled old edge exactly compensates. Deleting the five sites recovers the original support, so the transformation is parsimonious. This identifies an all-host-equivalent residual with just one optional port of degree four. It does not determine its unrestricted complexity.
