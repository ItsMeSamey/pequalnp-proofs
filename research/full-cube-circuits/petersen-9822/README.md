# Full-cube edge function L-meta-9822

The minimum unrestricted AND/OR/NOT circuit size lies between 16 and 18 inclusive. The offered problem asks whether every circuit needs at least 18 gates.

The 18-gate circuit uses the original ten inputs numbered 0 through 9. Each row defines the next wire from two earlier wires. The independent checker evaluates all 1,024 input assignments.

Identifying inputs 0 and 3 and relabeling the remaining inputs gives the nine-input function in L-meta-11026. Applying the same substitution to the input wires of any circuit preserves its gate count, including every NOT gate. The published lower bound of 16 for the nine-input function therefore applies here. The checker verifies the complete edge image. [Published Lean theorem](https://github.com/open-goat/pequalnp-proofs/blob/aecf602ea3c8da01533a13d2ca03b633689f3033/lean/PEqualNP/Outside/L_meta_11026.lean)

Run `python3 verify.py` from this directory to check both calculations.
