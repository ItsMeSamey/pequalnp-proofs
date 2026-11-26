import ThresholdThirdDeletion

namespace ThresholdThirdDeletion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity T2SoleOrSplice ThresholdPublicMinimum

theorem circuit_tenth (regular : RegularTenth) {n : ℕ} (large : (2:ℕ)^402≤n)
    (C : Circuit) (mono : Monotone2 C) (computes : Computes n C) :
    let z := (C.size:ℝ)-2*(n:ℝ)-Real.sqrt (2*(n:ℝ))
    0≤z ∧ (n:ℝ)^3≤((2:ℝ)^15*z)^10 := by
  let z := (C.size:ℝ)-2*(n:ℝ)-Real.sqrt (2*(n:ℝ))
  change 0≤z ∧ _
  obtain ⟨hz,hp⟩ := unrestricted regular large
  have least : (minimum n:ℝ)≤(C.size:ℝ) := by exact_mod_cast le_size mono computes
  have sz : surplus n≤z := by dsimp [surplus,z]; linarith
  have scaled := mul_le_mul_of_nonneg_left sz (show (0:ℝ)≤2^15 by norm_num)
  exact ⟨hz.trans sz,hp.trans (pow_le_pow_left₀ (mul_nonneg (by norm_num) hz) scaled 10)⟩

#print axioms circuit_tenth
end ThresholdThirdDeletion
