# Constructing a switch setting with blossom matching

The solve(sigma, r, s) function in involutive_blossom.py takes the off-output permutation, grouped into cyclic triples by input switch. It returns an integer mask or None. It checks the forbidden-turn involution and uses the fixed-wire splitting in involutive-forbidden-turns.md. Its only local dependency is check_involutive_turns.py.

For each pair of conjugate arcs introduce two port vertices joined by a reference matching edge. If one arc runs from u to v, label its entry port u and its mate's entry port v′. Choosing an orientation of this matching edge chooses the corresponding directed arc. Add an edge between conjugately labeled ports on different reference edges. Add two exposed terminals, one adjacent to ports labeled R and one adjacent to ports labeled S′, using the outgoing copy at the start and the incoming copy at the finish.

A regular simple directed path uses each arc pair at most once. Its sequence of oriented reference edges therefore extends to a simple augmenting path. Conversely an augmenting path uses each reference edge at most once, hence yields a directed walk using at most one arc of each pair even if wire vertices repeat. Drop fixed-wire bridge arcs and loop-erase the physical walk to preserve turn compatibility. Read the gate states from the remaining path and set unused gates to zero.

A perfect matching exists exactly when the reference matching has an augmenting path. The implementation finds a maximum-cardinality matching, follows the terminal component of its symmetric difference with the reference matching, and returns the decoded mask. The matching graph has linearly many vertices and polynomially many edges. NetworkX blossom takes cubic time in the number of vertices.
