import ThresholdSharpLowerFinal

namespace ThresholdSharpGlobalLower
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity T2SoleOrSplice ThresholdPublicMinimum ThresholdThirdDeletion

/-- The eventual bound with its arity cutoff independent of the circuit. -/
theorem circuit_lower_sharp (ε : ℝ) (ep : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit, Monotone2 C → Computes n C →
      let z := (C.size : ℝ) - 2*(n:ℝ) - Real.sqrt (2*(n:ℝ))
      0 ≤ z ∧ (9765625-ε)*(n:ℝ)^3 ≤ 2048*z^10 := by
  obtain ⟨N, hN⟩ := lower_sharp ε ep
  refine ⟨N, ?_⟩
  intro n hn C hm hc
  let z := (C.size : ℝ) - 2*(n:ℝ) - Real.sqrt (2*(n:ℝ))
  change 0 ≤ z ∧ _
  obtain ⟨hz, h⟩ := hN n hn
  have minle : (minimum n : ℝ) ≤ (C.size : ℝ) := by exact_mod_cast le_size hm hc
  have gap : surplus n ≤ z := by dsimp [surplus, z]; linarith
  exact ⟨hz.trans gap, h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz gap 10) (by norm_num))⟩

#print axioms circuit_lower_sharp
end ThresholdSharpGlobalLower
