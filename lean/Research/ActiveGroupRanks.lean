import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators Classical

namespace LayoutActive

theorem active_count_le_range_finrank {K γ : Type*} [Field K]
    {X Y : γ → Type*} [∀ g, AddCommGroup (X g)] [∀ g, Module K (X g)]
    [∀ g, FiniteDimensional K (X g)] [∀ g, AddCommGroup (Y g)] [∀ g, Module K (Y g)]
    (G : Finset γ) (M : (g : γ) → X g →ₗ[K] Y g) :
    (G.filter (fun g => M g ≠ 0)).card ≤ ∑ g ∈ G, Module.finrank K (LinearMap.range (M g)) := by
  classical
  calc
    _ = ∑ g ∈ G, (if M g ≠ 0 then 1 else 0 : ℕ) := by
      simpa only [Nat.cast_id] using (Finset.sum_boole (R := ℕ) (fun g => M g ≠ 0) G).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro g _
      by_cases h : M g = 0
      · simp [h]
      · rw [ite_eq_left h]
        exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr
          (fun hz => h (LinearMap.range_eq_bot.mp hz)))

end LayoutActive
