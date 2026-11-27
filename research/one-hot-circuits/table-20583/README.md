# Upper bounds for the L-meta-20583 table

The official target is **1,350 gates**. The strongest construction identified here uses **1,500**, leaving 150 gates to save. The upstream theorem L_meta_19358 contains that construction on the same 128-by-128 table. Its 128 hexadecimal rows match the rows for L-meta-20583 exactly. Replaying its 1,500 gates at output wire 1,755 agrees on all 16,384 promised inputs. [Upstream Lean source](https://github.com/open-goat/pequalnp-proofs/blob/aecf602ea3c8da01533a13d2ca03b633689f3033/lean/PEqualNP/Outside/L_meta_19358.lean)

This fork also records independent [1,625-gate](./1625-gates/README.md) and [1,785-gate](./1785-gates/README.md) constructions. Both packages contain original-domain evaluators and their own netlists. The earlier 2,630-gate figure described a construction baseline.
