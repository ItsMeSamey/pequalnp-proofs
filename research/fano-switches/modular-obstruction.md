# Uniform modular marker counts can vanish on a feasible subcubic tree

For every k≥2 there is a single tree of maximum degree three and two rank-three labelings having the same multiset of nonzero vertex labels. In both labelings the numbers of even induced supports in *all eight* output classes vanish modulo k. The target 111 is feasible under exactly one of the labelings. Thus even the full vector of counts, or all its Walsh character sums, modulo any prescribed finite list of moduli cannot alone decide feasibility. Use the least common multiple for a list.

Write e₁,e₂,e₃ for the coordinate labels. Start with a path u–v–w–r. At r attach two disjoint pendant paths with N−2 and N−1 new vertices. Set N to a multiple of three for which F_N=0 modulo 2k. Such N exists and can be taken at most (2k)² times three: the update on consecutive Fibonacci residues is a permutation starting at (0,1). Take three times its period. Use F₀=0,F₁=1.

Label every vertex except u,v,w by e₃. For the no-instance use labels (e₁,e₂,e₃) on u,v,w. Both u and v would be selected for target 111, giving leaf u odd induced degree. For the yes-instance use (e₁,e₃,e₂). The set consisting of u,w and the first vertex of either pendant path is independent and realizes 111.

In a tree, an induced even-degree subgraph has no edge, since any finite nontrivial tree component has a leaf. Its even supports are exactly its independent sets. On a path of length m **in vertices**, the independent-set count is F_{m+2}. The difference between the even- and odd-cardinality counts obeys d₀=1,d₁=0,d_m=d_{m−1}−d_{m−2}; it is zero whenever m≡1 mod 3. At m=N−2 both counts are exactly F_N/2, a multiple of k. All path labels are e₃, so either permitted output increment has multiplicity divisible by k.

Condition on an independent selection on u,v,w,r. If r is absent, the first tail is a free m-vertex path. If r is present, the first vertex on the second tail is absent, leaving a free m-vertex suffix. Either way this factor annihilates every output-class count modulo k before the remaining choices are summed. The proof does not address algorithms that choose additional moduli in response to the instance or use structural information about the graph.

Run `python -B check_modular.py` for direct checks.
