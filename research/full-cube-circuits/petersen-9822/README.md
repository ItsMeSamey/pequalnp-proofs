# Full-cube edge function L-meta-9822

The minimum unrestricted AND/OR/NOT circuit size is either 17 or 18. Independent source and finite-ledger reviews establish the lower bound of 17 for the full ten-input Boolean cube. The offered problem asks whether every circuit needs at least 18 gates. [Complete 39-file lower-bound and construction replay](signed16-cert/README.md)

The lower bound combines two results. A signed realization with free inversion still needs at least 16 binary gates. Thus any physical circuit of total size at most 16 would be monotone. The independently checked monotone size lower bound is 17. The signed proof uses the first binary gate, a fanout count, the three-shared-gate lower bound, and the exhaustive exclusion of the three- and four-shared-gate cases. Independent full-cube checks covered 249 and 84 cases respectively. This composition has mathematical and computational review. The partial Lean replay below covers the earlier 15-binary deduction. [Three shared gates](physical/third-fork.md) · [Three-gate exclusion](reductions/three-shared.md) · [Four-gate exclusion](reductions/four-shared.md) · [Monotone size bound](monotone-seventeen.md)

At total size 17, the remaining possibilities are a monotone circuit with exactly seven ANDs, or a circuit with one NOT and 16 binary gates. The offered lower bound of 18 remains open.

The 18-gate circuit uses the original ten inputs numbered 0 through 9. Each row defines the next wire from two earlier wires. The independent checker evaluates all 1,024 input assignments.

Identifying inputs 0 and 3 and relabeling the remaining inputs gives the nine-input function in L-meta-11026. Applying the same substitution to the input wires of any circuit preserves its gate count, including every NOT gate. The published lower bound of 16 for the nine-input function therefore applies here. The checker verifies the complete edge image. [Published Lean theorem](https://github.com/open-goat/pequalnp-proofs/blob/aecf602ea3c8da01533a13d2ca03b633689f3033/lean/PEqualNP/Outside/L_meta_11026.lean)

Run `python3 verify.py` from this directory to check both calculations.

For monotone circuits, a size-17 candidate must contain at least two distinct internal AND gates that each accept a nonedge pair. The two pairs can differ. [Rank-two flattening](nonedge-products/rank-two-flattening.md) · [Single exceptional product that accepts a singleton](nonedge-products/sole-hot.md) · [Single exceptional product that rejects singletons](nonedge-products/sole-cold.md)

For unrestricted circuits with at most 17 gates, at least ten gates must be OR or NOT, leaving at most seven AND gates. The proof excludes every possibility with exactly nine OR/NOT gates under the independent binary-gate floor. This earlier argument alone left sizes 16 and 17 open. [Four-inversion exclusion and dependencies](nonedge-products/four-inversions-paid.md)

Every circuit requires at least ten OR or NOT gates even when the number of AND gates is unrestricted. It also requires at least fifteen binary gates even if inversion is free. The earlier 15-binary bound allowed two NOT gates at size 17. The 16-binary bound above reduces that allowance to one. The monotone minimum lies between 17 and 18. Before the 16-binary bound, these facts restricted size 16 to one NOT gate. The fifteen-binary-gate deduction uses the checked signed face of L-meta-9825. [Ten OR or NOT gates](nonedge-products/unrestricted-ten-paid.md) · [Fifteen binary gates](physical/binary-fifteen.md) · [Monotone lower bound](monotone-seventeen.md)

The monotone proof first bounds the number of AND gates by six. The receiver argument covers four or fewer AND gates. Separate enumerations cover five AND gates and six AND gates at a total cost of at most sixteen. Both archives include native code, replay instructions and the enumerated outcomes. [Receiver argument](directions.md) · [Five-AND archive](five-and/five-SHA256SUMS) · [Six-AND archive](six-and-cap16/six16-SHA256SUMS)

Any monotone 17-gate realization must use exactly seven AND gates. The six-AND case was eliminated by an exhaustive native computation covering 41,719 profiles. Independent review checked the search programs, the profile coverage and the archived results. For a 16-gate realization with one NOT, the function feeding the NOT must have minimal positive supports with empty intersection. [Six-AND search and replay](six17-cert/README.md) · [Single-NOT support restriction](nonedge-products/cap16-compulsory.md) · [Ninth-vertex cofactor](verification/h9.md)

In the remaining seven-AND monotone case, a 17-gate realization requires at least three nonfull conditional activations in the reverse search. The archive includes the profile accounting, replay programs and positive controls. [Scope and replay](seven-two-cert/scope.md)

The signed binary lower-bound deduction now has a Lean replay from the precise prior face hypothesis. The trial checked the deduction and its helper modules. Completing an end-to-end replay of the supplied wrapper requires the published numerical face certificate. [Lean replay scope](physical/signed-floor-replay.md)
