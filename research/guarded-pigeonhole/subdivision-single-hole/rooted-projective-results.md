# Rooted four-space projection records

The input is a binary point set P requiring F(p)≠0 for an unknown linear map to binary two-space. A required line a,b,a+b pins F(a)=1, F(b)=2 without loss for existence: every solution has distinct nonzero images for a,b, and a unique change of output basis gives this rooting. Root counts are counts with that choice fixed.

The implementation holds affine equations on the 2d map bits. For each distinct span W of four initial points (or all points if fewer than four), choose a canonical basis. Reduce the at most eight local evaluation forms modulo the ambient affine equations, retaining all linear dependencies with their constants. These describe exactly the projection, by linear extension. Filter its at most 256 local maps by the nonzero obligations currently known on W. An empty filter certifies rejection. Otherwise add affine equations valid on every survivor and nonzero points on W nonzero under every survivor. A record supplies the chosen basis and the added statements; replay recomputes the table at that point of the proof. replay_unsat additionally requires a final empty local table. Finite stability alone does not certify satisfiability. The local maps and proof records use no enumeration of global assignments.

On the indicated deterministic cycle bases, rooted at the first sorted required line, the following results were reproduced.

| Graph | Cycle dimension | Distinct spaces | Result | Final affine dimension | Records |
|---|---:|---:|---|---:|---:|
| Petersen | 6 | 291 | Refuted in first pass | 1 before final contradiction | 12 |
| Cube | 5 | 67 | Stable | 3 | 3 |
| Flower J5 | 11 | 14,751 | Stable | 15 | 3 |
| Flower J7 | 15 | 73,332 | Stable | 23 | 3 |

The cube has eight surviving affine assignments and exactly four true rooted maps. The flower fixed points are inconclusive. An independent 27-state transfer computation counts zero proper labeled three-edge-colorings for J5, J7, J9. Its state is the triple of colors on the three inter-claw track edges. Successive triples u,v are allowed when their coordinatewise binary differences are the three distinct nonzero colors, supplying the three spoke colors. Closing the tracks swaps the last two positions. The even-length four-claw control has 96 colorings. Another 200 seeded small affine systems verified every computed local table against unrestricted global enumeration. The flower outcomes pertain to the tested rooting and fixed initial-point scopes.
