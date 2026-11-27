# Full-cube edge function L-meta-9822

The minimum unrestricted AND/OR/NOT circuit size lies between 16 and 18 inclusive. The offered problem asks whether every circuit needs at least 18 gates.

The 18-gate circuit uses the original ten inputs numbered 0 through 9. Each row defines the next wire from two earlier wires. The independent checker evaluates all 1,024 input assignments.

Identifying inputs 0 and 3 and relabeling the remaining inputs gives the nine-input function in L-meta-11026. Applying the same substitution to the input wires of any circuit preserves its gate count, including every NOT gate. The published lower bound of 16 for the nine-input function therefore applies here. The checker verifies the complete edge image. [Published Lean theorem](https://github.com/open-goat/pequalnp-proofs/blob/aecf602ea3c8da01533a13d2ca03b633689f3033/lean/PEqualNP/Outside/L_meta_11026.lean)

Run `python3 verify.py` from this directory to check both calculations.

For monotone circuits, a size-17 candidate must contain at least two distinct internal AND gates that each accept a nonedge pair. The two pairs can differ. [Rank-two flattening](nonedge-products/rank-two-flattening.md) · [Single exceptional product that accepts a singleton](nonedge-products/sole-hot.md) · [Single exceptional product that rejects singletons](nonedge-products/sole-cold.md)

For unrestricted circuits with at most 17 gates, at least ten gates must be OR or NOT, leaving at most seven AND gates. The proof excludes every possibility with exactly nine OR/NOT gates under the independent binary-gate floor. It still leaves candidates of total size 16 and 17. [Four-inversion exclusion and dependencies](nonedge-products/four-inversions-paid.md)

Every circuit requires at least ten OR or NOT gates even when the number of AND gates is unrestricted. It also requires at least fifteen binary gates even if inversion is free. Thus a 17-gate circuit has at most two NOT gates. The monotone minimum lies between 17 and 18. Together these bounds imply that any 16-gate circuit has exactly one NOT gate. The fifteen-binary-gate deduction uses the checked signed face of L-meta-9825. [Ten OR or NOT gates](nonedge-products/unrestricted-ten-paid.md) · [Fifteen binary gates](physical/binary-fifteen.md) · [Monotone lower bound](monotone-seventeen.md)
