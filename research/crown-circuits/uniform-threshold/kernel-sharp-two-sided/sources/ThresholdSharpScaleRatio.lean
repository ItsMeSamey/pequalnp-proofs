import ThresholdNativeRatio
import ThresholdSharpScaleChoice
namespace ThresholdSharpScaleBand
theorem coarse_ratio (P X t E : ℝ) (pp : (2:ℝ)^80≤P) (px : P≤X)
    (time : X^10=t) (large : 1≤E) (band : E≤P*X^6) :
    (2:ℝ)^50*(1+max 0 E)≤t ∧ (2:ℝ)^200≤t := by
  have x1 : 1≤X := by norm_num at pp; linarith
  have xn : 0≤X := by linarith
  have lower : (2:ℝ)^80≤X := pp.trans px
  have pow4 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2^80) lower 4
  have xwide : X^4≤X^10 := pow_le_pow_right₀ x1 (by decide)
  have mult := mul_le_mul_of_nonneg_right lower xn
  have sqfour : X^2≤X^4 := pow_le_pow_right₀ x1 (by decide)
  have lowP := mul_le_mul_of_nonneg_left px (show (0:ℝ)≤2^51 by norm_num)
  have room : (2:ℝ)^51*P≤X^4 := by norm_num at mult lowP ⊢; linarith
  have m := mul_le_mul_of_nonneg_right room (pow_nonneg xn 6)
  have budget := mul_le_mul_of_nonneg_left band (show (0:ℝ)≤2^51 by norm_num)
  rw [max_eq_right (by linarith : 0≤E),←time]
  constructor
  · nlinarith only [m,budget,large]
  · norm_num at pow4 ⊢; linarith
#print axioms coarse_ratio
end ThresholdSharpScaleBand
