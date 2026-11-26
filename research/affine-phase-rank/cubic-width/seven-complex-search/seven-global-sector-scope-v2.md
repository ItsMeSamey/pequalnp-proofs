# Seven stabilizer rays for three CCZ copies, by product count

Fix the three original three-qubit blocks. A block-product ray factors across all three as a product of three stabilizer rays. A ray entangled only across one pair still counts as an entangled exception. The target is the tensor cube of the normalized CCZ phase state, and the representation permits arbitrary complex coefficients and arbitrary nine-qubit stabilizer rays. The unrestricted lower bound is seven, so a list of seven witnessing equality would have seven linearly independent rays with nonzero coefficients. The product of three one-copy, two-ray decompositions gives the upper bound eight.

| Block-product rays | Entangled rays | Exact seven-term sector |
|---:|---:|---|
| 0 | 7 | Open |
| 1 | 6 | Open |
| 2 | 5 | Open |
| 3 | 4 | Open |
| 4 | 3 | Open |
| 5 | 2 | Open. The reviewed search reduction currently leaves 13 terminal resource-profile orbits (54 labeled profile pairs). |
| 6 | 1 | Excluded by the one-exception normal-form analysis. |
| 7 | 0 | Excluded by exact block-product rank eight. |

The five-product analysis preserves the five original product terms during its cut transfers, then uses the structure of the remaining pair to restrict or replace that pair. There is no established conversion of an arbitrary list with three or more entangled rays into this sector. The terminal ledger counts equivalence classes of resource multiplicities under simultaneous party permutations and exchange of exceptional rays. A class contains many independently encoded physical pairs. Some removed classes can be replaced by other classes; their removal certifies that one need not search them separately.

The Fourier sparsity bound for four arbitrary stabilizers limits the number of elements of a particular native product dictionary that a seven-list can contain. The native dictionary is a subset of block-product rays. A bound on native terms alone gives no upper bound of the same size on block-product terms.

## Dependencies

- Unrestricted lower bound: rank-seven-lower.md and rank-seven-manifest.sha256.
- Block-product sector: seven-product-exclusion.md.
- One-exception sector: single-entangled-profile.md, sole-biseparable-exclusion.md, single-bell-ghz-exclusions.md, single-entangled-ghz-four.md, single-mixed-ghz-bell-exclusion.md, single-two-link-bell-exclusion.md, and sole-bell-path-exclusion.md.
- Two-exception ledger: terminal-13-after-path-and-triangle.txt, incorporating triangle-double-ghz-companion.md and simple-ghz-path-rectangle.md. Later reviewed sector-specific improvements may supersede this dated count.
- Native dictionaries: four-rays-arbitrary-controls.md.
