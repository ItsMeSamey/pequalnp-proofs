# Affine hulls with an adjacent root pair pinned

For a simple graph with adjacent vertices 0,1, require x0=x1=1 and x_i(Ax)_i=0 over GF(2) for every vertex. The question here is whether polynomial calculus derives **every affine equation true on all pinned supports**. The tests compare equation spaces before adding any proposed equation or its negation.

Let P be the set of pinned support vectors. An affine equation c+h·x=0 is valid exactly when (c,h) is orthogonal to the span of (1,x) over x in P. Thus one rank computation tests every simultaneous choice of vertex weights, including arbitrary nonsingleton weights. For the empty set that span is zero and every equation is valid. On the PC side, compute the full ordinary Boolean degree-bounded closure with a degree-ordered echelon basis. Multiply each new pivot below the degree cutoff by each variable, reduce squares and continue to closure. The linear-or-constant pivots span all affine equations attainable at that bound. Soundness makes dimension equality sufficient; the Python analyzer additionally reports explicit bases and missing forms.

Substitution of the two pins preserves PC degrees two and three. Their guards then force the two linear root-neighbor parities. The second implementation eliminates those as well, using affine substitutions, before taking closure. Substituted quadratic guards lift to the original system within degree two by using the eliminated linear equations one factor at a time. Original linear consequences are recovered by adjoining the solved coordinate equations and lifting residual forms. Run `python -B analyze.py 386 25 352 194 34 20 12 9 5` to see the exact supports and bases. The mask encoding for an affine equation puts its constant at bit zero and the coefficient of x_i at bit i+1.

## Exhaustive results

For unrestricted simple graphs, degree two recovers every hull through six vertices. At seven vertices, 57 of the 6,564 rooted graph representatives have a strict quadratic hull gap, among 5,902 nonempty fibers. At eight vertices the counts are 6,293 gaps among 125,120 representatives and 119,229 nonempty fibers. Degree three recovers every hull in both censuses. Root exchange and permutation of nonroot vertices are quotiented. An example in the first failing dimension has adjacency masks 82,49,104,20,11,6,5. Its three pinned supports have masks 19,23,103. The equation x3=0 belongs to the exact hull but degree two misses it.

For bipartite graphs degree two first fails at nine vertices. In the following table the roots are distinguished by side. All permutations fixing the roots within each side are quotiented. Up to swapping the entire sides, all positive split sizes are covered. The table counts nonempty fibers of strict PC2 gaps; all empty fibers refute at degree two. Degree three recovers all affine invariants through twelve vertices. For smaller sizes, padding by isolated vertices and assigning those new coordinates zero shows that the upper bounds descend.

| Vertices | PC2 gaps by increasing smaller side (starting at 1) | PC3 gaps |
| ---: | --- | ---: |
| 8 | 0, 0, 0, 0 | 0 |
| 9 | 0, 0, 0, 17 | 0 |
| 10 | 0, 0, 0, 195, 786 | 0 |
| 11 | 0, 0, 0, 1,176, 10,278 | 0 |
| 12 | 0, 0, 0, 5,052, 77,800, 175,756 | 0 |

The explicit nine-vertex bipartite example above has pinned supports 139,143,171,311,335. All obey x3+x6+x7=0, which degree two fails to derive. The oracle's original-coordinate affine rank is five, with two pin equations included. Degree two has rank four; degree three has rank five.

Compile `check.cpp`, `bipartite.cpp` and `interiors.cpp` separately using `c++ -O3 -std=c++17`. The code uses the GCC/Clang unsigned 128-bit extension. The first program takes n and a draw count (zero for exhaustive search, positive for random edge-density sampling). The second takes n and the size of the left side, with left root 0, and works through n=10. The interior enumerator takes the same two arguments and is intended for n=10,11,12 with left size at least two. It canonizes the graph left after deleting the two roots, and then quotients root-attachment choices by that interior's automorphism group. At the balanced ten-vertex split the two independent programs agree on 45,884 representatives, 36,160 nonempty fibers and 786 quadratic gaps. At 6+6 the second algorithm checked 3,481,936 representatives with 3,152,315 nonempty fibers. A one-vertex side gives a star forest and the pinned edge is always a bridge.

Separately, 20,000 randomly generated unrestricted graphs at each of n=9,10 gave no cubic gap. There were 778 and 690 quadratic gaps respectively. These larger unrestricted results are samples and do not establish universal completeness.

## Multiple active residual components

Delete the pinned roots. Let a,b be their neighborhood vectors on the remaining vertices, and put d=a+b. The residual guards are x_i((Bx)_i+d_i)=0 and the root equations are a·x=b·x=1. Summing guards on each residual component C yields d_C·x_C=0, so only a·x=1 needs to be imposed separately.

Without the root parity condition, the span of feasible supports on C is exactly the hyperplane d_C·x_C=0 (the entire space if d_C=0). Each zero-defect vertex gives a singleton. A shortest path between marked vertices with no marked interior gives a feasible support, as its endpoints have degree one and its interior degree two. The graph on marked vertices linked by such paths is connected when there is at least one mark: take any connecting walk in C, split it at marks, then shorten within each segment's permitted vertices. Subtract the available singleton interiors to obtain all marked-pair sums. These vectors span the asserted space.

Call C active if its local marker a_C takes one on some feasible support; equivalently a_C is outside the span of d_C. If at least two components are active, every pinned affine equation is a combination of the component equations and the root parity equation, hence degree two derives the full hull. To prove this, vary one component within a fixed marker fiber, using a different active component to balance the global bit. A universal weight must be constant on each local fiber. Its value on the zero fiber is zero because the empty support is available. Thus on each active component it agrees on feasible supports with a scalar multiple of the marker. Realizations with a single active component contributing one force that scalar to agree across all active components. Inactive components allow every local feasible support and contribute only their known component equations. With exactly one active component, any additional affine invariant must come from its marker-one fiber. With none active, summing component equations and using the marker gives a quadratic refutation. Equivalently, an adjacent root pair admits a support exactly when its edge lies on a cycle: a shortest alternate path gives an induced cycle, whereas a bridge cut gives a degree-two contradiction.

Run `python -B verify.py` for 104 independent basis comparisons at degrees two and three in the ordinary polynomial ring with explicit Boolean axioms, repeated powers, and both original pin equations. These checks include the two explicit affine-hull gaps and 50 reproducible random graphs.
