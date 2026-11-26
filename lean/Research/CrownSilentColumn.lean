import Research.CrownSilentReachDefs
import Research.CrownSilentIncidence
namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem silent_column_capacity (C : Circuit) (R : Finset (Fin 24))
    (copy : ∀ r ∈ R, ∀ a, r ∈ rawSupport C a →
      (C.wires (List.replicate 24 false)).getD a false = false → rawSupport C a = {r})
    (k : Fin C.gates.length) (hk : k ∈ silentGates C R) :
    (R.filter (fun r => silentIncident C r k)).card ≤ if silentBoth C R k then 2 else 1 := by
  classical
  have cold := chargeable_cold C k (Finset.mem_filter.mp hk).2.1
  let L := R ∩ rawSupport C (operand C k 0)
  let T := R ∩ rawSupport C (operand C k 1)
  have cap (a : ℕ) (hc : (C.wires (List.replicate 24 false)).getD a false = false) :
      (R ∩ rawSupport C a).card ≤ 1 := by
    rcases (R ∩ rawSupport C a).eq_empty_or_nonempty with he | ⟨r,hr⟩
    · simp [he]
    · obtain ⟨hR,hs⟩ := Finset.mem_inter.mp hr
      rw [copy r hR a hs hc]
      exact (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
  have lc : L.card ≤ 1 := cap _ cold.1
  have tc : T.card ≤ 1 := cap _ cold.2
  have eu : R.filter (fun r => silentIncident C r k) = L ∪ T := by
    ext r; simp [L,T,silentIncident]; tauto
  have bc : silentBoth C R k = true ↔ L.Nonempty ∧ T.Nonempty := by
    simp [L,T,silentBoth,Finset.Nonempty]
  rw [eu]
  by_cases b : silentBoth C R k = true
  · simp only [b,reduceIte]; exact (Finset.card_union_le ..).trans (by omega)
  · simp only [b]
    have e : L = ∅ ∨ T = ∅ := by
      by_contra! ne
      exact b (bc.mpr ne)
    rcases e with e|e <;> simp_all
end PEqualNP.Research.MissingCell
