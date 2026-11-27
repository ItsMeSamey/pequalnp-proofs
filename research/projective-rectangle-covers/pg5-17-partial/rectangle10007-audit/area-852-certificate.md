# Area 851 exclusion by a real rank correction

Assume seventeen all-zero rectangles cover every zero of the 31-by-31 projective incidence matrix. Areas count all rectangle cells with multiplicity. The prior finite-field-area.md and repeated-classes.md rule out area below 851. At area 851 the excess above the 775 zero cells is 76. Starting from the 75 possible one-shore histograms in repeated_classes.py, the exact rational inequality in diagonal-constraint.md leaves the three histograms below. On each shore, list a row type by its positive excess entries and its multiplicity. Any unlisted type has zero count.

| Single 1 | Single 2 | Single 3 | Single 4 | Split (3,1) | Split (1,1) | Rejection |
|---:|---:|---:|---:|---:|---:|---|
| 4 | 12 | 12 | 1 | 2 | 0 | Binary pencil condition |
| 5 | 9 | 13 | 3 | 0 | 1 | Ternary quadratic condition |
| 7 | 7 | 13 | 4 | 0 | 0 | Pair count with both shores of this type |

The first two filters are in split-margin-notes.md and split_margin.py. They depend only on the histogram on the chosen shore and apply before rectangle maximalization. Therefore the last histogram must occur on both shores. The positive excess cells then form a partial permutation. Each unordered pair of covering rectangles can meet at most once: if it shared two disjoint cells, their off-diagonal corners would also be shared, producing two excesses in one row. Sharing two cells in a single row or column is already precluded. The defect histogram requires 7·1+7·3+13·6+4·10=146 intersecting unordered rectangle pairs. Seventeen rectangles supply only 136. Thus area 851 is impossible whether or not the rectangles are maximal. The result constrains a putative 17-cover and leaves its existence open.

Local replay runs python diagonal_constraint.py 76 in this directory. The three types and the first two filters are printed at the end.
