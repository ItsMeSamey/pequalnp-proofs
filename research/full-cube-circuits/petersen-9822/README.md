# Full-cube edge function L-meta-9822

The minimum unrestricted AND/OR/NOT circuit size lies between 16 and 18 inclusive. The offered problem asks whether every circuit needs at least 18 gates.

The 18-gate circuit uses the original ten inputs numbered 0 through 9. Each row defines the next wire from two earlier wires. The independent checker evaluates all 1,024 input assignments.

Identifying inputs 0 and 3 and relabeling the remaining inputs gives the nine-input function in L-meta-11026. Applying the same substitution to the input wires of any circuit preserves its gate count, including every NOT gate. The published lower bound of 16 for the nine-input function therefore applies here. The checker verifies the complete edge image. [Published Lean theorem](https://github.com/open-goat/pequalnp-proofs/blob/aecf602ea3c8da01533a13d2ca03b633689f3033/lean/PEqualNP/Outside/L_meta_11026.lean)

Run `python3 verify.py` from this directory to check both calculations.

For monotone circuits, a size-17 candidate must contain at least two distinct internal AND gates that each accept a nonedge pair. The two pairs can differ. [Rank-two flattening](nonedge-products/rank-two-flattening.md) · [Single exceptional product that accepts a singleton](nonedge-products/sole-hot.md) · [Single exceptional product that rejects singletons](nonedge-products/sole-cold.md)

For unrestricted circuits with at most 17 gates, at least ten gates must be OR or NOT, leaving at most seven AND gates. The proof excludes every possibility with exactly nine OR/NOT gates under the independent binary-gate floor. It still leaves candidates of total size 16 and 17. [Four-inversion exclusion and dependencies](nonedge-products/four-inversions-paid.md)

Every circuit requires at least ten OR or NOT gates even when the number of AND gates is unrestricted. It also requires at least fifteen binary gates even if inversion is free. Thus a 17-gate circuit has at most two NOT gates. The monotone minimum lies between 17 and 18. Together these bounds imply that any 16-gate circuit has exactly one NOT gate. The fifteen-binary-gate deduction uses the checked signed face of L-meta-9825. [Ten OR or NOT gates](nonedge-products/unrestricted-ten-paid.md) · [Fifteen binary gates](physical/binary-fifteen.md) · [Monotone lower bound](monotone-seventeen.md)

The monotone proof first bounds the number of AND gates by six. The receiver argument covers four or fewer AND gates. Separate enumerations cover five AND gates and six AND gates at a total cost of at most sixteen. Both archives include native code, replay instructions and the enumerated outcomes. [Receiver argument](directions.md) · [Five-AND archive](five-and/five-SHA256SUMS) · [Six-AND archive](six-and-cap16/six16-SHA256SUMS)

Any monotone 17-gate realization must use exactly seven AND gates. The six-AND case was eliminated by an exhaustive native computation covering 41,719 profiles. Independent review checked the search programs, the profile coverage and the archived results. For a 16-gate realization with one NOT, the function feeding the NOT must have minimal positive supports with empty intersection. [Six-AND search and replay](six17-cert/README.md) · [Single-NOT support restriction](nonedge-products/cap16-compulsory.md) · [Ninth-vertex cofactor](verification/h9.md)

In the remaining seven-AND monotone case, a 17-gate realization requires at least three nonfull conditional activations in the reverse search. The archive includes the profile accounting, replay programs and positive controls. [Scope and replay](seven-two-cert/scope.md)

The signed binary lower-bound deduction now has a Lean replay from the precise prior face hypothesis. The trial checked the deduction and its helper modules. Completing an end-to-end replay of the supplied wrapper requires the published numerical face certificate. [Lean replay scope](physical/signed-floor-replay.md)
