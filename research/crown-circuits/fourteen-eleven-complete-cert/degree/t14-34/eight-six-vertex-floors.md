# Four-plus-six components on the ten-flag boundary

The ten-flag decoder has eight ORs. Against a degree-four center in the six-vertex component, the layer bound gives at most three ORs to erase the remote four vertices. For the other possibilities the six-flag graph is subcubic and has eight or nine edges. Six vertices with positive degrees admit exactly five connected subcubic simple graphs with eight edges, and two with nine (the prism and the complete bipartite three-by-three graph). The four-flag partner is K4 or the diamond respectively.

For each of these seven graphs, eight-six-vertex-floors.py supplies an injection of a graph from degree/t13-seven/graph-cut/initial-drat.tsv whose four-OR decoder formula with free ANDs was proved unsatisfiable. The script enumerates NetworkX's complete graph atlas and tests the images of the checked edges under every injection into six vertices. Rejecting every individual edge and accepting every edge-pair union in the larger graph implies the same requirements on the subgraph. Consequently the six-flag decoder retains at least five ORs.

Thus in every case the four-vertex component can cost at most three ORs to erase. The role-based proof of eight-and-four-vertex-remote.md uses only this allowance after its introductory layer calculation. Its branching deletion step peels any remaining remote component down to an anchor, using an edge-versus-its-union-with-a-central-edge witness, before applying the six-flag OR floor. The private-product argument then shows that the remote actually costs at least four. No four-plus-six physical candidate survives.

| NetworkX atlas | Host mask | Archived obstruction | Injection, zero-based |
|---|---:|---:|---|
| G143 | 14451 | 1532 | 0,5,3,2,1,4 |
| G151 | 27237 | 3452 | 1,4,3,5,2,0 |
| G152 | 20261 | 3885 | 5,1,2,4,3,0 |
| G153 | 7781 | 3948 | 2,4,0,5,1,3 |
| G154 | 22181 | 3576 | 5,1,3,4,2,0 |
| G174 | 23211 | 7916 | 5,3,0,1,4,2 |
| G175 | 22189 | 7672 | 5,3,1,4,2,0 |

Masks use triangular bit index max(i,j)(max(i,j)−1)/2+min(i,j).
