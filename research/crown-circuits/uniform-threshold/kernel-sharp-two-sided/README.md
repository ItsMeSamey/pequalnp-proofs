# Two-sided third-order term for threshold two

Let C(n) be the minimum size of a monotone circuit of fan-in at most two computing threshold two on the full Boolean cube. Write z(n) = C(n) − 2n − √(2n). For every real ε > 0 there is N such that for every integer n ≥ N, z(n) ≥ 0 and

(9765625 − ε)n³ ≤ 2048 z(n)¹⁰ ≤ (9765625 + ε)n³.

Thus z(n)/n^(3/10) converges to 5/2^(11/10). The kernel endpoint [ThresholdSharpTwoSided.rational](sources/ThresholdSharpTwoSided.lean) states the signed tenth-power inequalities. The original compiler reported only propext, Classical.choice and Quot.sound. The [manifest](ThresholdSharpTwoSided-manifest.tsv) locks 304 local sources. An independent clean replay rebuilt all 304 project and local modules and two additional pinned Mathlib prerequisites. The terminal axiom report matched byte for byte. See the [replay receipt](independent-replay/receipt.json) and [verification result](independent-replay/independent-check.txt).
