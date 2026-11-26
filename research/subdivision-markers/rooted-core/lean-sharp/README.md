# Formal counting bound for opposite witnesses

Lean 4.36 compiled `SharpOpposite.sharp_bound` with exit status zero and empty diagnostics. It proves `n ≤ 2^t` from `Data n (t+1)`. The certificate assumes the chart data defined in the source. The construction of these data from native witnesses is given in the [mathematical proof](../sharp-opposite-core.md). An axiom listing for this declaration was pending at this release.

The producer's `check.sh` uses a local Lean 4.36 mathlib installation in the shared reference checkout.
