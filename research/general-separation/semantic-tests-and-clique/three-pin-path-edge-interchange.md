# Interchanging the one-edge and two-edge pin patterns

Let G be any simple graph with three distinct named vertices required to lie in an induced subgraph whose degrees are all even. Choose two of the pins u,v. Add a new vertex w adjacent exactly to u and v, toggle the old edge uv, and replace u by w among the named pins. All other old edges and both other pin names stay as given.

In every witness on the new graph, w and v are selected. The degree at w is 1+x_u, so its required evenness forces u selected as well. At each of u,v, toggling the old edge to the other selected vertex changes the degree parity by one, and the newly selected neighbor w changes it a second time. All other old vertices see the same selected neighbors as before. Hence deleting w from any witness is a witness on the starting graph. Conversely every starting witness extends by selecting w; its two neighbors were already selected. The two maps are inverse and preserve every original occupancy bit, including the old pin u. This whole construction adds exactly one degree-two vertex.

If the named vertices induce a two-edge path, take u as its middle vertex and v as either endpoint. The move subdivides uv. The two retained old pins are nonadjacent and w meets just v among them, producing exactly one pin edge.

If the named vertices induce exactly one edge, take u as the isolated named vertex and v as either endpoint of that edge. The move adds the triangle u,v,w over the previously absent uv. The two retained old pins remain adjacent and w meets just v among them, producing a two-edge pin path.

This gives deterministic many-one reductions in both directions, with exact witness recovery and equal counts. After substituting named pins as ones, the new w guard is the linear equation x_u+1=0. Eliminating that equation leaves exactly the original pin and guard system modulo binary Boolean axioms. Accordingly, refutability at each formal polynomial-calculus degree D≥2 agrees as well: restriction x_u=1 transports the expanded proof down, and the linear equation allows all quadratic generators at that restriction to be recovered in degree two for a proof in the other direction.
