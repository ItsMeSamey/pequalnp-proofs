# Widths still requiring a general argument

For a normalized separator of size at most 33, the published mixed-gate floor and the complete 22-mixed case leave m=23,…,33. In a live mixed cone with P point inputs and L line inputs the read surplus is k=m+1−P−L≥0. If g and c are the paid point and line gate counts, g+c≤33−m. Line separation gives L≥7 and c≥L−7. The point-width price results give P≥11, g≥9 at P=11, and g≥5 at P=12.

The width-independent seven-line result excludes k≤3, the eight-line result excludes k≤1, and the nine-line read-once result excludes k=0. These rules apply at all m under the total-33 hypothesis. Additionally the complete-cell primary results for m=23 exclude every case at P=11 or 12 and L=7,11 at P=13. A candidate surviving this accounting may still violate the terminal-clean normal form, pivotal repair, or stricter point/line bank prices. The grid does not certify realizability. Results stated for a particular price or circuit shape do not remove the whole width cell.

| m | Pure-gate budget | Remaining width cells | Point widths represented |
|---|---:|---:|---|
| 23 | 10 | 6 | 13–14 |
| 24 | 9 | 20 | 11–15 |
| 25 | 8 | 25 | 12–16 |
| 26 | 7 | 32 | 12–17 |
| 27 | 6 | 37 | 12–18 |
| 28 | 5 | 39 | 12–19 |
| 29 | 4 | 38 | 13–20 |
| 30 | 3 | 35 | 13–21 |
| 31 | 2 | 29 | 13–22 |
| 32 | 1 | 21 | 13–23 |
| 33 | 0 | 11 | 13–23 |

At m=23 each of P=13 and P=14 has L=8,9,10 left as whole-cell obligations. At every other level remaining-widths.tsv records every surviving P,L, its k, and the separate maximum point/line costs. Those two maxima share the total budget. remaining.py reproduces the grid. The terminal-clean structural constraints apply to an appropriately normalized minimal witness; they should not be imposed on arbitrary original bank cells without a width-preserving argument.

The P13/L11 certificate uses the pinned L-meta-18968 sample. Independent source review checked the split on missing singleton lines, the point-price limits, and the private-sensitivity tests against the preceding point catalogues. Its bulk numerical exclusion uses the producer execution. [P13/L11 certificate](w13-eleven/P13L11-m23.zip)
