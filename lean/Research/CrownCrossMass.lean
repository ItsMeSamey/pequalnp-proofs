import Research.CrownTightMass

namespace PEqualNP.Research.MissingCell
open scoped BigOperators

def overlapMass {I : Type*} [DecidableEq I] (w : I → ℚ) (H B : Finset I) : ℚ :=
  (∑ i ∈ H, w i) + ∑ i ∈ H ∩ B, w i

theorem overlap_discount_eq {I : Type*} [DecidableEq I] (H B : Finset I) (w : I → ℚ) :
    overlapMass (fun i => if i ∈ B then w i / 2 else w i) H B = ∑ i ∈ H, w i := by
  classical
  have eq : H ∩ B = H.filter (· ∈ B) := by ext i;simp
  rw [overlapMass,eq,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i ∈ B <;> simp [h]

theorem overlap_mass_mono_weights {I : Type*} [DecidableEq I] (H B : Finset I) {w v : I → ℚ}
    (le : ∀ i, w i ≤ v i) : overlapMass w H B ≤ overlapMass v H B :=
  add_le_add (Finset.sum_le_sum (fun i _ => le i)) (Finset.sum_le_sum (fun i _ => le i))

theorem overlap_mass_mono_set {I : Type*} [DecidableEq I] {H K : Finset I} (B : Finset I)
    (w : I → ℚ) (pos : ∀ i, 0 ≤ w i) (sub : H ⊆ K) : overlapMass w H B ≤ overlapMass w K B :=
  add_le_add (Finset.sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => pos i))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_inter_right sub) (fun i _ _ => pos i))

end PEqualNP.Research.MissingCell
