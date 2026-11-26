# Two fundamental cycles suffice for the unsigned approximation

Let a finite family of at least two simple paths in a tree have a nonempty common set of edges H. This set is a path with distinct endpoints u and v. Label each member by its continuation edge beyond u and beyond v. At an endpoint where a member terminates give it its own fresh label. Neither coordinate is constant. A constant edge label would extend H, and fresh labels cannot be constant across the family.

Some two members have distinct labels in both coordinates. Indeed, choose two with different first labels. If their second labels agree, any member with a different second label must differ from one of them in its first label as well. The resulting pair has common edge set exactly H.

For a fixed shortest-path tree, the intersection of two or more distinct fundamental cycles contains only tree edges. Every nonempty such intersection therefore equals the edge intersection of two of the cycles. If each single fundamental cycle and each XOR of two has zero unsigned score in an abelian group, the twice-weighted score of each pair intersection vanishes. Every term involving at least two cycles in the parity inclusion-exclusion expansion then vanishes, since its coefficient is a multiple of two. Consequently the XOR of the entire family scores zero.

At a root on an optimal nonzero simple cycle, each fundamental cycle of a non-tree edge on that cycle costs at most the optimum. Their XOR equals the optimal cycle. The preceding lemma gives a nonzero single cycle or a nonzero XOR of two. Its edge-disjoint simple-cycle decomposition has a nonzero member of cost at most twice the optimum, for nonnegative costs. This includes parallel edges and loops, whose tree-path edge set can be empty.
