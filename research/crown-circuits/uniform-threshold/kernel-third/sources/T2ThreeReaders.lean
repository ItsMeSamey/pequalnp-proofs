import T2RawReader

namespace ResidualSurplus

/-- Distinct physical row IDs prevent charging either operand slot twice. -/
theorem three_closed_credits (xs : List Item) (Q : Nat → Bool) (p d t : Item)
    (pd : p.1 ≠ d.1) (pt : p.1 ≠ t.1) (dt : d.1 ≠ t.1)
    (pa : p ∈ xs) (da : d ∈ xs) (ta : t ∈ xs)
    (pc : closedReader Q p = true) (dc : closedReader Q d = true)
    (tc : closedReader Q t = true) :
    3 ≤ (xs.filter (closedReader Q)).length := by
  let ids := (xs.filter (closedReader Q)).map Prod.fst
  have mem (z : Item) (hz : z ∈ xs) (hc : closedReader Q z = true) : z.1 ∈ ids.toFinset := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨z, List.mem_filter.mpr ⟨hz,hc⟩, rfl⟩
  have sub : ({p.1,d.1,t.1} : Finset Nat) ⊆ ids.toFinset := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact mem p pa pc
    · exact mem d da dc
    · exact mem t ta tc
  have h := (Finset.card_le_card sub).trans ids.toFinset_card_le
  simpa [ids,pd,pt,dt] using h
end ResidualSurplus
