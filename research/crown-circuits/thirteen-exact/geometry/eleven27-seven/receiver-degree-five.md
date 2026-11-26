# Degree five in the 13-label receiver graph

Use the regular 31-gate, seven-AND interface in `receiver-articulations.md`. There are 13 edges, and every pure flag has degree three or four. Suppose at least four flags are pure. Then the receiver graph has maximum degree four.

Degree six and above already exceed the gate budget on the neighbor slice. For degree five, take a vertex x with five neighbors. It is mixed. Drop every component containing neither x nor a pure flag. Setting its flags false contracts one distinct dedicated decoder OR per vertex. The retained decoder thus still has at most q−2 ORs on its q flags.

In the component of x, peel layers outside its closed neighborhood, charging one OR for every removed vertex. Every other retained component contains an edge: fix an anchor edge, peel all vertices outside its endpoints with the same path test, then erase the anchor pair. The anchor pairs charge one more OR apiece using the union of a fixed central edge with each anchor edge. These are the disjoint input changes in the certificate argument of `receiver-layers.md`. With c detached components the OR lower bound is q+d−5−c. Therefore d=5 forces c≥2, and each detached component contains a pure flag by the choice of components retained.

If the component of x contains two or more pure flags, choose two. The five center edges supply each at most one incident edge. To complete the two flags to degree three takes at least three more edges, because only one edge can join them. The component therefore has at least eight edges, and two detached pure-bearing components use at least three each. This exceeds 13.

If the component of x contains one pure flag, it takes at least seven edges. At least three more pure flags lie in two or more detached components. A component containing two takes at least five edges; a component containing one takes three. Thus the detached components require at least eight edges.

If the component of x contains no pure flag, select four detached pure flags meeting at least two components. Three together require at least six edges and an additional separate flag takes three. Two pairs in separate components require at least five edges each. Splitting into more components only increases the minimum. The five edges incident to x and the nine detached exceed 13.
