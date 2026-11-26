import ThresholdFourThirdsArithmetic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ByContra

namespace ThresholdFourThirds

/-- Recover the real lower bound without assuming the integer excess is nonnegative. -/
theorem to_real {n s : ℤ} (hn : 0 ≤ n) (h : Bound n s) :
    (4 / 3 : ℝ) * Real.sqrt ((n : ℝ) + 3) - 6 ≤ (s : ℝ) := by
  obtain ⟨hp, hsq⟩ := h
  have hp' : (1 : ℝ) ≤ (s : ℝ) + 6 := by exact_mod_cast hp
  have hs' : (16 : ℝ) * ((n : ℝ) + 3) ≤ 9 * ((s : ℝ) + 6) ^ 2 := by
    exact_mod_cast hsq
  have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hroot := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 3 by linarith)
  by_contra! bad
  have hm : 0 < (4 * Real.sqrt ((n : ℝ) + 3) - 3 * ((s : ℝ) + 6)) *
      (4 * Real.sqrt ((n : ℝ) + 3) + 3 * ((s : ℝ) + 6)) :=
    mul_pos (by linarith) (by linarith [Real.sqrt_nonneg ((n : ℝ) + 3)])
  nlinarith

theorem uniform_real (C : ℕ → ℤ) (base : 1 ≤ C 2)
    (step : ∀ n : ℕ, 2 ≤ n →
      C n + 3 ≤ C (n + 1) ∨ Nonempty (Regular ((n + 1 : ℕ) : ℤ) (excess C (n + 1))))
    {n : ℕ} (hn : 2 ≤ n) :
    2 * (n : ℝ) + (4 / 3 : ℝ) * Real.sqrt ((n : ℝ) + 3) - 6 ≤ (C n : ℝ) := by
  have h := to_real (n := (n : ℤ)) (by exact_mod_cast (Nat.zero_le n))
    (uniform_squared C base step hn)
  unfold excess at h
  push_cast at h
  linarith

end ThresholdFourThirds
