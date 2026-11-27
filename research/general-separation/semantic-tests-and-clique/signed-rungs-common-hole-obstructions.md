# Two ways a signed two-sheet lift accepts a common-hole NO

Take a ten-vertex source with square rims x,a,b,d and y,A,B,D in cyclic order. Add paths a–u–A and b–v–B. This is simple, biconnected, subcubic, and the named nonadjacent vertices x,y have degree two. Every cycle through x,y must cross both connecting paths as they are its only routes between rims. It must use the a–b rim arc containing x, and the A–B rim arc containing y. Thus its edges omit ab and AB, both chords. There is no induced cycle through the two names.

For each original vertex make two physical sites indexed by a sheet bit. Along every original edge connect equal sheets, except along xa and yA where the sheets are exchanged. Include vertical edges between the two copies of each site, so that a doubled site with one selected horizontal neighbor at each copy is legal. Prescribe exactly the three physical pins x₀,a₁,y₀. Their only mutual edge is x₀a₁. The twist at each named site is on exactly one of its incident edges.

First select x₀,a₁,b₀,d₀ and y₀,A₁,B₀,D₀ together with u₁,v₀. In cyclic order these are

    a₁, x₀, d₀, b₀, v₀, B₀, D₀, y₀, A₁, u₁.

They induce a single physical cycle. The only possible additional horizontal edges project to ab or AB; these edges are straight but their selected ends have opposite sheets. Every vertical edge has only one selected endpoint. Thus the physical witness is connected and uses exactly one copy of every original vertex, yet its projected cycle has two chords. Enforcing exclusivity at every original site alone cannot fix this translation.

Second, leave both connecting paths' interiors vacant. On the first rim choose x₀,a₁,b₁,d₁,d₀ and on the other y₀,A₁,B₁,D₁,D₀. Each list in the displayed order induces a five-cycle closed back to its initial site, using just the rung at d or D. They are disjoint induced cycles satisfying the same pins. More generally an odd-voltage chordless rim lifts to such an induced cycle upon doubling any chosen ordinary site and using its rung: the path obtained by deleting that site lifts with endpoints attaching to opposite copies, precisely because the total voltage is odd. In the two-rim construction the rims may be enlarged, with the attachment pairs still adjacent and the named sites on the long rim arcs. The two doubled sites can then be arbitrarily far from the names.

These examples address horizontal matching lifts with two twists and optional vertical rungs. The connected counterexample persists if all rungs are removed. They do not establish impossibility for translations checking projected chords through additional coupled constraints.

The [terminal-local counterexample](terminal-local-hole-obstruction.md) proved the source two-rim obstruction by a different switch argument. The present ten-site witness tests the actual colored adjacency, native three pins, chord visibility, and vertical corrections on the lifted graph.
