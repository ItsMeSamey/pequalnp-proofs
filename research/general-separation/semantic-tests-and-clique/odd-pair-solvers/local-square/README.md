# Two prescribed vertices on graphs with locally bounded degree

The solver finds an induced all-odd subgraph containing both prescribed vertices, or certifies infeasibility, in polynomial time on a recognized class of simple graphs. Every vertex lying on a triangle or on a four-cycle containing an edge in at least three four-cycles must have degree at most four. Other vertices can have arbitrarily large degree. The solver also tests this condition after folding interchangeable vertices. Outside its complete cases it can return UNKNOWN. [Theorem and proof](unbounded-degree-local-square-walk.md)

The module routine protects both named vertices and records how to lift a core witness to the original labels. For each r ≥ 2, a module-prime graph on 4r + 4 vertices has a unique pinned witness containing all r degree-five vertices. These examples have pathwidth at most three. [Construction](prime-degree-five-diamond-chain.md)

For replay, extract the [quartic release](../odd-pair-polynomial-quartic-release.zip) into a working directory and copy the files in this directory there. With NetworkX available, run the three scripts local_square_window_check.py, pin_module_odd_core.py and degree_five_periodic_prime.py. The local-square oracle comparison covers 24,684 original graph/pin pairs.
