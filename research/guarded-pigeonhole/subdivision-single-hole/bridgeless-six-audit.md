# At least ten signatures on six same-shore tips

Let a connected bipartite cubic multipole have six tips, all on A, and a bridgeless ordinary internal graph. Every holder is distinct: two tips sharing a holder would leave at most one internal incidence there. Counting degrees gives |A|=|B|+2.

Choose any two tips to receive red and remove their two holders from the internal graph. For any nonempty S in B, write N for its original neighborhood. Counting incidences gives
$$3(|N|-|S|)=t(N)+|\delta(S\cup N)|,$$
where t counts tips. If S together with N is the whole graph then the surplus is two. Otherwise connectedness and bridgelessness imply the cut has size at least two. Thus the surplus is at least one. If both removed holders belong to N, at least two tips belong there as well, raising the surplus to at least two. In all cases at least |S| neighbors survive. Hall's theorem gives an internal perfect matching after deletion.

Use that matching and the two prescribed tips for red. Each residual cycle can alternate the other colors and each of the two residual paths joins tips on the same shore, requiring opposite colors at its ends. The independent choices of path orientations yield precisely two of the three pair partitions on the remaining four tips. Record these witnesses for each of the fifteen choices of the red pair. Every complete partition has only three pairs, so the thirty incidences yield at least ten distinct partitions. The missing partitions share no pair with each other. This is a lower bound and a constructive list; it does not determine all missing partitions in general.

Subdivide the six edges of K4 once each and attach one tip at each subdivider. Direct enumeration gives 120 proper labeled assignments on fourteen distinct partitions from the 1296 permutations at the four original vertices. The missing partition pairs each edge with its unique disjoint opposite edge. Adding those three cap edges gives the Petersen graph, independently checked by graph isomorphism in check_subdivided_k4.py.
