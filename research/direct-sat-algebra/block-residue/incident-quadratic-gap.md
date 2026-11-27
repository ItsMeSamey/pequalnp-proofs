# A growing gap between linear consequences of quadratic equations and the exact oriented span

A block has indexed edges AB, BC, BD, CD₁, CA, CD₂ in that order. Pair consecutive edges. Glue k copies only at A. In cycle coordinates ABC, BCD₁ and CD₁+CD₂, the three products of dual evaluations are x(x+y), y(y+z), and xz. Their off-diagonal terms are distinct, so no nonzero linear consequence results from adding these polynomials. Blocks use disjoint cycle coordinates; the same conclusion holds jointly.

The actual binary dual solutions have x=0 and y implies z. Indeed x=1 forces y=1, then z=1, contradicting xz=0. The three remaining solutions span the plane x=0. Across copies the span is the direct sum of these planes. Its annihilator, the intersection of all oriented column spans, has dimension k. Each pair has distinct, nonzero line directions, so the direct intersection and nesting steps cannot initiate a reduction either.

Degrees are 2k at A and 3, 4, 3 at each copy's B, C, D, counting both indexed CD edges. For k≥2 there is no degree-two site. Signs do not affect this span comparison. In each block choosing AB, BD, CD₂ yields three independent columns, so every signed target is existentially feasible. This separates two ways to certify universal directions; it gives no decision hardness.

The scheduled checker uses the actual forest-chord order CD₁, CA, CD₂, in which the guaranteed direction is the CA unit. It checks the exact hull against every orientation, then realizes signed choices through raw occurrence copies, pins, and the original NAND circuit.
