# Signed tenth-power lower bound for threshold two

For n ≥ 2^402, let C be any unrestricted-fanout monotone circuit of fan-in at most two computing threshold two on the full Boolean cube. Put z = C.size − 2n − √(2n). The Lean endpoint proves both z ≥ 0 and n³ ≤ (2¹⁵ z)¹⁰. By monotonicity, the mathematical consequence is z ≥ 2⁻¹⁵ n^(3/10).

The original serial build compiled the two signed-power endpoints with the three standard axioms. The manifest fixes all 187 sources. The direct real-power formulation and sharp leading coefficient require separate formal receipts.

[Native declarations](sources/ThresholdPublicThird.lean) · [Axiom receipts](axioms.log) · [Portable manifest](ThresholdPublicThird-manifest.tsv)
