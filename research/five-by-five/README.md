# Five-gate lower bounds for twenty promise graphs

Every listed 5-by-5 graph contains a 3-by-3 submatrix with minimum circuit size at least six, even allowing NOT gates. On the selected nine inputs, the other input wires are fixed zero. A five-gate implementation of the larger graph therefore induces a five-gate computation on the selected nine rows. The certificate enumerates gate signatures on those rows, accounting for out-of-range reads, nullary gates and unary NOT semantics. It follows the finite normalization and search from accepted L_meta_17187. The proof uses no native_decide, added axiom, or external solver.

The aggregate modules [FiveGate238](../../lean/Research/FiveGate238.lean) and [FiveGate94](../../lean/Research/FiveGate94.lean) use the accepted L_meta_17187 normalization in [FiveGateTransfer](../../lean/Research/FiveGateTransfer.lean). Two further existence statements have direct circuit witnesses in [FiveByFive19363](../../lean/Research/FiveByFive19363.lean) and [FiveByFive19364](../../lean/Research/FiveByFive19364.lean).

| Step | Mask | Obstruction | Ordered rows | Ordered columns |
|---|---:|---:|---|---|
| 19317 | 3247678 | 238 | (0, 1, 2) | (0, 1, 4) |
| 19318 | 3247934 | 238 | (0, 1, 2) | (0, 1, 3) |
| 19319 | 7576638 | 94 | (0, 2, 1) | (0, 1, 3) |
| 19320 | 7576886 | 94 | (0, 2, 1) | (0, 1, 4) |
| 19321 | 7577150 | 238 | (0, 1, 2) | (0, 1, 4) |
| 19322 | 7577382 | 94 | (1, 2, 0) | (1, 0, 3) |
| 19323 | 7577398 | 238 | (0, 1, 2) | (0, 1, 4) |
| 19324 | 7577402 | 238 | (0, 1, 2) | (0, 1, 3) |
| 19325 | 7644470 | 94 | (0, 4, 1) | (0, 1, 4) |
| 19326 | 7712116 | 94 | (0, 4, 1) | (0, 2, 4) |
| 19327 | 16227576 | 94 | (0, 3, 1) | (0, 3, 4) |
| 19328 | 16235644 | 94 | (0, 2, 1) | (0, 2, 4) |
| 19329 | 16236082 | 238 | (0, 1, 2) | (0, 1, 4) |
| 19330 | 16236086 | 238 | (0, 1, 2) | (0, 1, 4) |
| 19331 | 16236156 | 238 | (0, 1, 2) | (0, 2, 4) |
| 19332 | 16238126 | 94 | (1, 3, 0) | (1, 0, 4) |
| 19333 | 24151086 | 94 | (0, 4, 1) | (0, 1, 3) |
| 19334 | 24489316 | 94 | (1, 4, 0) | (2, 0, 3) |
| 19335 | 24894510 | 94 | (0, 2, 1) | (0, 1, 3) |
| 19336 | 24894758 | 94 | (1, 2, 0) | (1, 0, 3) |
