import Lean.Elab.Tactic.Omega

namespace ProtectedIncidence

/-- If every wire in a directed subgraph supplies one slot plus its
    fanout excess, vertices using both operands internally need sources. -/
theorem two_operand_nodes_le_sources {n₀ n₁ n₂ extra : Nat}
    (slots : n₁ + 2 * n₂ ≤ n₀ + n₁ + n₂ + extra) : n₂ ≤ n₀ + extra := by
  omega

/-- One round pays for its removed inputs and an additional gate. -/
theorem round_ledger {original current next removed batch rounds : Nat}
    (prior : current + 2 * removed + rounds ≤ original)
    (now : next + 2 * batch + 1 ≤ current) :
    next + 2 * (removed + batch) + (rounds + 1) ≤ original := by
  omega

/-- The original plane has twice N inputs; the theta residual pays for
    every remaining input down to the additive constant four. -/
theorem terminal_ledger {sites remaining removed rounds residual original : Nat}
    (sites_eq : remaining + removed = sites)
    (paid : residual + 2 * removed + rounds ≤ original)
    (theta : 2 * remaining ≤ residual + 4) :
    2 * sites + rounds ≤ original + 4 := by omega

/-- A round of size at most 24 and the risk-neighborhood separation lemma
    give the concrete reservoir size in the order-401 proof. -/
theorem mark_bound_401 {marks : Nat}
    (packing : marks * (376 * 376 - 38808) ≤ 38808 * (376 - 1)) :
    marks ≤ 141 := by omega

/-- If no useful batch or simplification exists, the number of OR groups
    must satisfy incompatible lower/upper bounds. Raw fanout of protected
    sites appears explicitly as the term 2*guarded + excessRaw. -/
theorem group_ledger_401
    {remaining sole guarded excessRaw excessGate internalSources twoLarge
      privateAnd allAnd groups : Nat}
    (surviving : 322406 ≤ remaining + 38808)
    (sole_cap : sole ≤ 13075)
    (protected_cap : guarded ≤ 4602)
    (excess_cap : excessGate + excessRaw ≤ 14688)
    (sources : 25 * internalSources ≤ 644812)
    (large_slots : twoLarge ≤ internalSources + excessGate + 2 * guarded + excessRaw)
    (private_cap : privateAnd ≤ sole)
    (ands : allAnd ≤ privateAnd + twoLarge)
    (tops : groups + privateAnd ≤ 1 + excessGate + 2 * allAnd)
    (thin : remaining ≤ 2 * groups + sole + guarded) : False := by
  omega

theorem specialization_401 {gates : Nat} (h : 646425 ≤ gates) :
    (401^2 + 401 + 1) * 401 ≤ 100 * gates := by omega

end ProtectedIncidence
