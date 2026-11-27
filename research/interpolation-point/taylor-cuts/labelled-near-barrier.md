# Residue matching near a supplied Tutte barrier

Given a vertex set B, let d=|B|−o(G−B), where o counts odd components. For a perfect matching M write t_C for the number of matching edges between B and component C, and a for the number of matching edges internal to B. Parity gives t_C congruent to |C| modulo two. Summing over B gives

d = 2a + Σ_even t_C + Σ_odd (t_C−1).

Negative slack proves infeasibility. Every odd component with t_C=1 is ordinary. Mark the B endpoints of internal edges, edges into even components, and edges into nonordinary odd components. For a nonordinary odd component t_C≥3, so t_C≤3(t_C−1)/2. The number of marked vertices is at most floor(3d/2).

Enumerate only the marked B vertices and assignments of their partners by endpoint, enforcing disjointness. Reject any marked odd component touched fewer than three times or with the wrong parity. For each fixed pattern, enumerate attainable local matching gains on the remaining vertices of all nonordinary and even components by a least-vertex subset DP. Convolve these tables with the label-option tables of the fixed endpoint pairs. Each lookup retains one tuple of original edge IDs per gain. No edge between two different components of G−B is possible.

The remaining B vertices must match the ordinary odd components bijectively. For a vertex u and component C, each possible attachment uv and each internal matching gain of C minus v define a bipartite macro edge. Deduplicate equal gains at that macro endpoint pair while retaining a representative original trace. For each fixed-side gain ask the sharpened bipartite solver for the remaining target. Each original matching is represented by its marked pattern and each constructed solution decodes into an original perfect matching. The solver verifies returned IDs against the full vertex set and requested syndrome.

For maximum component size k, dimension b and original order N, internal matching tables cost O*(2^k 3^{O(b)}) per component. Endpoint enumeration has N^{O(d)} possibilities. Each surviving pattern needs at most 3^b bipartite queries on at most |B| pairs. A supplied component-size or slack cap can return UNKNOWN before search; a capped bipartite answer can leave a target unresolved.

For K_{r+2} completely joined to r disjoint triangles, B the clique has slack two and maximum component size three. Label clique edges one and all others zero over GF(3). Residue zero requires one triangle with three attachment edges, and residue one requires one internal clique edge. Residue two is impossible. The checker uses r=3 and also enumerates original matchings on random multigraphs.
