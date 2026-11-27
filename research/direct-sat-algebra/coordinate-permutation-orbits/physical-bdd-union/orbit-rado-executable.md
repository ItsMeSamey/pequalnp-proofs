# Four-position orbit executable

Call orbit_rado.solve(rotation,flip,start,zero,ones=0,*,assignment_cap=None). Pair positions are lexicographic, followed by numeric difference 0 through 3. Permutations map an old position to a new one. Noncanonical arrays, dimensions or start produce skip. Invalid input masks or assignment cap raise ValueError. The zero-dimensional singleton-vertex case is supported.

On SAT the tuple word contains conjugate exponents, not generator IDs. For each j apply inverse rotation j times, one flip, then forward rotation j times. The solver independently forms the final physical state by positive rotations and checks the original zero and one pins. UNSAT follows a contradictory pin, a proved affine contradiction or exhaustive failure on a core component. assignment_cap limits tested core basis functionals only; polynomial recognition, preprocessing, intersections and replay lie outside it. At exhaustion the result is skip. An early exit's component-rank list covers visited components. This is a decision procedure and does not count extensions.

For q residual rows on h≤2m dimensions, there are ≤q+2 linear/partition matroid-intersection calls, at most q augmentations per call, ≤3q indexed items, ≤q Gaussian pivots per reduction and polynomial-bit provenance. Each reduction sorts its pivot indices. At most h preprocessing restarts occur. Each component of rank r costs ≤2^r polynomial-time iterations and polynomial space. Physical replay uses ≤2m(2m+1) generator moves on arrays of length D=2m(m−1), with polynomial D-bit integer work per move. Cost counters are algorithmic quantities rather than machine instructions.

Implementation: orbit_rado.py and rado_matroid.py. Proof: orbit-rado-kernel.md. Independent checker: check_rado.py.
