import ThresholdScaleRoot

namespace ThresholdUpperBeta

/-- Pick the same coefficient for every order, using only integer powers. -/
theorem exists_beta : ∃ β : ℝ, 1 ≤ β ∧ β ≤ 2 ∧ β ^ 5 = 8 := by
  obtain ⟨β, lo, pow⟩ := ThresholdScaleRoot.exists_above (k := 5) (b := (1:ℝ)) (t := 8)
    (by decide) (by norm_num) (by norm_num)
  refine ⟨β, lo, ?_, pow⟩
  by_contra! bad
  have h := pow_lt_pow_left₀ bad (by norm_num : 0 ≤ (2:ℝ)) (by decide : 5 ≠ 0)
  rw [pow] at h
  norm_num at h

#print axioms exists_beta
end ThresholdUpperBeta
