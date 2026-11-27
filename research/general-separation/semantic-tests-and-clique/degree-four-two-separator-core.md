# A two-site shore already suffices at the degree-four middle pin

Start with any simple graph G and three required distinct vertices p,q,r. Toggle the edge pq. Add seven new vertices a,h,c,U,V,s,d, make a,h,c the required vertices, and add exactly the edges
[
ah, hc, ar, cs, hU, hV, Up, Vq, Vr, Vs, sd, dU.
]
The pin path a–h–c has ambient degrees (2,4,2). The transformation preserves each individual witness and its unique lift.

The endpoint equations force r=s=1. The middle equation then requires U=V=t. At s, its three neighbors c,V,d require d=1+t. If t=0, d=1 but exactly one of its neighbors s,U is selected. Therefore U=V=1 and d=0. Vertex U sees h,p,d, forcing p=1. Vertex V sees h,q,r,s, forcing q=1. On the original vertices the new contribution at p and q is one apiece, canceled by the toggled edge pq between selected pins. Vertex r sees two new selected neighbors a,V. Thus restricting any witness to G solves the original instance. Conversely every original witness lifts by adding a,h,c,U,V,s and leaving d vacant.

After removing the selected pin path, the required odd sites in the forced branch are r,s,U,V. Removing the two sites U,V leaves the original left shore G△pq, with the designated odd endpoint r, and the right edge s–d, with the designated odd endpoint s. Their two interface columns have binary rank two on each shore. When G△pq is connected, {U,V} is an inclusion-minimal r–s separator. Deleting U alone leaves r–V–s, while deleting V alone leaves a path from r inside the left shore to p, followed by p–U–d–s. The connectedness proviso does not exclude a hard decision case: on a connected source toggling pq preserves connectivity unless pq is a bridge, in which case compulsory inclusion of both endpoints already implies NO. On a disconnected source, components can be decided separately, and any component with at most two compulsory vertices is elementary. The witness bijection itself requires no connectedness hypothesis.

With U,V selected, the right shore has the unique local support {s} and sends (0,1). For both separator vertices to be odd, the left shore must send (1,0), meaning p=1 and q+r=0. In its interior the two parity prescriptions are odd at p,q and even at every other selected vertex, including r, which must be selected. This identifies the simultaneous channel test exactly.

A connected source example separates individual tests. Let G be the path p–r–q. The left shore after toggling pq is a triangle. Under its mixed internal prescriptions its feasible supports are precisely the empty set, {p,q}, and {r}. The two individual readouts p=1 and r=1 both pass; their conjunction fails. Once r is genuinely imposed, the handshake equation fixes the XOR of the two channel bits, so testing one channel on that same support suffices.

This is an equivalence to the unrestricted three-pin graph language, including vertex-supported witnesses. It does not imply NP-hardness for that language. It exhibits a separator of physical rank two with one mandatory odd endpoint on each side, outside the pin-free rank-two replacement rule.
