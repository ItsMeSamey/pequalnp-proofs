# The middle-degree boundary for three pins on an induced path

Let the pins induce a path a–b–c. If b has degree at most three in the entire graph, decision and witness construction take linear time, with no degree bound elsewhere. At middle degree four, even if both endpoints have degree two, the problem already represents every unrestricted three-pin induced-even instance by a constant-size parsimonious transformation.

With a,b,c all selected, b must have even selected degree, hence exactly two when its ambient degree is at most three. Delete b and all its neighbors except a,c. If a and c connect in what remains, take a shortest such path and restore b to get an induced cycle. Conversely, removing b from any witness leaves exactly a,c of odd degree, so they are in the same component. No other neighbor of b was selected.

For the reduction take any graph G with distinct pins p,q,r. Toggle the old edge pq. Add five new vertices w,h,t,u,v and exactly these edges:

    wp  wh  ht  tu  hu  hv  up  ur  vp  vq  vr

Replace the mandatory set by {w,h,t}. These induce the path w–h–t with ambient degrees 2,4,2. In every feasible support w forces p, t forces u, and h's four neighbors w,t,u,v then force v. The neighbors of u are h,t,p,r; the selected first three force r. The neighbors of v are h,p,q,r; the other three force q. Thus all five new sites and the three original pins are selected.

Conversely add all five new sites to any original feasible support. Their induced degrees, in order w,h,t,u,v, are 2,4,2,4,4. Old p sees three new neighbors w,u,v and the toggled edge to selected q. Old q sees the new neighbor v and the toggled edge to selected p. Old r sees two new neighbors u,v. Every old parity is preserved. Deleting the five new sites exactly recovers the original support. The proof holds for all eight possible old pin-edge patterns and permits disconnected witnesses. In every transformed YES instance h has selected degree four, so the degree-two search alone misses every one.

A polynomial solver for the degree-(2,4,2) pin path would solve the unrestricted three-pin graph language. This reduction does not determine the complexity of standard SAT.
