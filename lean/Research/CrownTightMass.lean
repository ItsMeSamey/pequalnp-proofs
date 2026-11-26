import Research.CrownSingletonKraft

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open scoped BigOperators

theorem tight_discount_rigidity {I : Type*} [DecidableEq I] (T U : Finset I)
    (w : I → ℚ) (pos : ∀ i, 0 < w i)
    (cap : (∑ i ∈ T, w i) ≤ 1)
    (full : (∑ i ∈ T, if i ∈ U then w i / 2 else w i) = 1) :
    Disjoint T U ∧ (∑ i ∈ T, w i) = 1 := by
  let v (i : I) := if i ∈ U then w i / 2 else w i
  have le (i) : v i ≤ w i := by dsimp [v]; split <;> linarith [pos i]
  have eq : (∑ i ∈ T, w i) = 1 := le_antisymm cap (by
    rw [←full]; exact Finset.sum_le_sum (fun i _ => le i))
  refine ⟨Finset.disjoint_left.mpr ?_,eq⟩
  intro i hi hu
  have lt : v i < w i := by dsimp [v];rw [ite_eq_left hu];linarith [pos i]
  have h := Finset.sum_lt_sum (s := T) (f := v) (g := w) (fun j _ => le j) ⟨i,hi,lt⟩
  exact (ne_of_lt h) (full.trans eq.symm)

theorem tight_subset_rigidity {I : Type*} [DecidableEq I] (S T : Finset I)
    (w : I → ℚ) (pos : ∀ i, 0 < w i) (sub : S ⊆ T)
    (full : (∑ i ∈ S, w i) = 1) (cap : (∑ i ∈ T, w i) ≤ 1) :
    S = T ∧ (∑ i ∈ T, w i) = 1 := by
  have eq : S = T := by
    by_contra ne
    obtain ⟨i,hi,hn⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨sub,ne⟩)
    have ub := Finset.sum_le_sum_of_subset_of_nonneg (s := insert i S) (t := T) (f := w)
      (Finset.insert_subset hi sub) (fun j _ _ => (pos j).le)
    rw [Finset.sum_insert hn,full] at ub
    linarith [pos i]
  exact ⟨eq,eq ▸ full⟩
end PEqualNP.Research.MissingCell
