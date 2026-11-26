# Exact arithmetic circuits for seven-terminal grove polynomials

An explicit family of undirected multigraphs with seven specified terminals transfers the permanent lower bound to the exact formal polynomial of spanning forests realizing a prescribed (3,3,1) terminal partition. The same graphs give the lower bound for the weighted spanning-three-forest polynomial with three prescribed disjoint pair separations.

Over each characteristic-zero field, at sufficiently large graph size M, exact binary arithmetic circuits require exp(Ω((log M)²/(log log M)²)) gates. The reduction uses signed polynomial edge weights, extraction of one trivariate coefficient, and division by a nonzero normalizing scalar. Circuit access permits coefficient propagation at O((N+1)^6) arithmetic operations per gate for an N-by-N permanent. The underlying Boolean feasibility question with three fixed pair separations has a polynomial-time algorithm.

The lower bound uses the November 24 permanent theorem as a dependency. Its degree-component border lower bound implies the exact-circuit bound used here. [Pinned primary statement](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/build/intro.tex)

[Reduction](permanent-to-grove.md) · [Four-port signature](weighted-permutation.md) · [Independent audit](permanent-grove-audit.md)
