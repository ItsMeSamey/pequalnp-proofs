import Research.CrownDemandArithmetic

namespace CrownDemandArithmetic

/-- A per-label deficit of one quarter-unit may be paid by an injectively
assigned silent label with one unit of surplus. -/
theorem aggregate_excess (r c : L → ℕ) (shared bad silent : Finset L)
    (few : shared.card ≤ 5) (payment : bad.card ≤ silent.card)
    (pointwise : ∀ i, (if i ∈ shared then 0 else 2) + (if i ∈ silent then 1 else 0) ≤
      r i + c i + (if i ∈ bad then 1 else 0)) :
    14 ≤ ∑ i, (r i + c i) := by
  classical
  have chi (S : Finset L) : ∑ i : L, (if i ∈ S then 1 else 0 : ℕ) = S.card := by
    rw [← Finset.sum_filter]
    simp
  have two : ∑ i : L, (if i ∈ shared then 0 else 2 : ℕ) =
      (Finset.univ \ shared).card * 2 := by
    have flip (i : L) : (if i ∈ shared then 0 else 2 : ℕ) =
        (if i ∈ Finset.univ \ shared then 2 else 0 : ℕ) := by by_cases h : i ∈ shared <;> simp [h]
    simp_rw [flip]
    rw [← Finset.sum_filter]
    have same : Finset.univ.filter (fun i : L => i ∈ Finset.univ \ shared) = Finset.univ \ shared := by ext; simp
    rw [same]
    simp
  have s := Finset.sum_le_sum (s := (Finset.univ : Finset L)) (fun i _ => pointwise i)
  simp only [Finset.sum_add_distrib, two, chi] at s
  have left : (Finset.univ \ shared).card + shared.card = 12 := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ shared)
  rw [Finset.sum_add_distrib]
  omega
end CrownDemandArithmetic
