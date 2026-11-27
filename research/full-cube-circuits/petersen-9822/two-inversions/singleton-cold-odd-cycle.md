# OR lower bound from an odd cycle of positive pairs

Let f be a binary monotone circuit function on n variables, false on singletons. Join u,v when f accepts the two-element input {u,v}. If this graph is connected and nonbipartite, every circuit for f has at least n−1 OR gates, regardless of its values on larger inputs.

A zero pin on an essential variable costs at least one OR when the remaining output is nonzero. Follow a live path from that variable to its first OR. Preceding ANDs become zero, forcing that OR to fold. An AND-only path to output would force remaining output zero. Choose a shortest odd cycle of length g; it is chordless. Peel vertices outside it in order of decreasing graph distance to the cycle. Each retained neighbor witnesses essentiality of its removed vertex and the cycle ensures nonzero output. This costs n−g ORs.

Suppose the restricted circuit uses at most g−2 ORs. Any single zero pin leaves a connected path on g−1 vertices and hence costs at least g−3 further ORs by peeling the path to one retained edge. Thus every vertex s has a unique first OR over all outgoing paths; two different first ORs would both fold on pinning s zero. An AND-only path to output is impossible.

Trim and minimize total size within the assumed OR budget. The earliest OR A combines two raw conjunctions. Let S be their combined support. Every path from any member of S to output passes through A. If S contains an edge, restriction to S is nonconstant and depends only on A, hence equals A. Thus A rejects all singletons. If S were proper, a crossing positive pair sx and the negative singleton x would have identical A and external bits. If S is the full cycle, A cannot supply g distinct minimal positive pairs using just two conjunctions.

Otherwise S is independent. Each member has an exterior neighbor, so A must accept each singleton in S to distinguish the corresponding edge from its exterior singleton. Two conjunctions can cover at most two singletons. A one-element S would make A a redundant raw alias. For S={u,v}, the nonadjacent vertices u,v must have identical neighbors, since the circuit cannot distinguish them in any exterior context. A chordless odd cycle contains no such pair. This proves the bound.

The singleton-cold K1 clamp for 9822 contains all original edges, so its positive-pair graph is connected and nonbipartite even if it gains new pairs. K1 therefore needs at least nine physical ORs.
