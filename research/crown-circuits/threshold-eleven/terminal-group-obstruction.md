# Eleven-input threshold two needs at least 26 monotone gates

A putative size-25 circuit must have seven ANDs and eighteen ORs by the six-AND lower bound and the threshold-two OR lower bound. Previously established consequences of the minor bounds are that each raw has exactly two consumers, both OR gates, that a pure OR operand of any AND has support at least four, and that every raw OR with support at most three has fanout one.

Flatten every fanout-one OR feeding an OR into its consumer. The resulting groups are binary OR trees. A group with k raw and t other leaves costs k+t−1 gates. A shared pure group's output counts as an ordinary signal leaf when it feeds another group. There are 22 raw occurrences in total. Repeated occurrences of a raw in one group could be contracted, contradicting minimality. Distinct raws cannot feed the same two groups because the singleton on one and the pair on both would then be indistinguishable at the output.

The groups therefore form the vertices of a simple graph with the eleven raw inputs as edges. Write p for the number of groups with t=0, called pure groups. Each pure group has degree at least four. Otherwise it has fanout one, so must feed an AND after flattening, or itself be the output. The support is too small for an AND operand, and a raw OR cannot compute threshold two.

Summing the gate costs yields 18 = 22 − p + Σ(t−1), where the sum is over nonpure groups. Hence p≥4 and the total of 22 raw occurrences gives 4p≤22. The two cases are p=4 and p=5. If e and f count pure–pure and nonpure–nonpure edges, the sum of pure degrees is 11+e−f. Thus e≥4p−11. The pure graph lacks at most one edge.

Set every raw outside the pure–pure edges to zero. Let z_i be the signal at pure vertex i. Each internal edge alone yields a rejecting input with exactly its two endpoint signals on. Every triple contains two distinct internal edges. Activating them gives a positive input with exactly those three vertex signals on. All remaining raw inputs to nonpure groups are now zero.

For p=4 all nonpure groups have t=1 and become wires. The residual circuit consists solely of ANDs on the z_i, so is a conjunction. To accept all four triples it must have empty support, which would accept every negative edge.

For p=5 exactly one nonpure group has t=2; the others have t=1. One OR and arbitrarily many ANDs give a disjunction of at most two conjunctions: the inputs to the only OR are conjunctions and any later conjunction of repeated copies of the OR collapses by idempotence. A conjunction supported on zero or one vertices accepts some negative edge since every vertex is incident to an internal edge. Each larger conjunction accepts at most three triples. Two such conjunctions cover at most six triples while the target accepts all ten.

Consequently size 25 is impossible. Together with the verified 27-gate construction, the unrestricted minimum for eleven-input monotone threshold two lies between 26 and 27.
