import ThresholdPublicMinimum
import ThresholdFourThirdsReal

namespace ThresholdPublicMinimum
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity T2SoleOrSplice

/-- The remaining circuit-side input. The excess is signed even though a
representative's size is natural. Smaller-arity deletion may return any benchmark circuit. -/
def NativeStep : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ C : Circuit, LexMinimum (n+1) C →
    (∃ D : Circuit, Monotone2 D ∧ Computes n D ∧ D.size+3≤C.size) ∨
    Nonempty (ThresholdFourThirds.Regular ((n+1 : ℕ) : ℤ)
      ((C.size : ℤ)-2*((n+1 : ℕ) : ℤ)))

theorem minimum_step (step : NativeStep) (n : ℕ) (hn : 2≤n) :
    intMinimum n + 3 ≤ intMinimum (n+1) ∨
      Nonempty (ThresholdFourThirds.Regular ((n+1 : ℕ) : ℤ)
        (ThresholdFourThirds.excess intMinimum (n+1))) := by
  have hn' : 2≤n+1 := by omega
  obtain ⟨C,hc,_⟩ := lex_at_minimum hn'
  rcases step n hn C hc with ⟨D,hm,hd,hs⟩ | hr
  · exact Or.inl (deletion_price hn' hc hm hd hs)
  · rw [representative_excess hn' hc]
    exact Or.inr hr

theorem minimum_squared (step : NativeStep) {n : ℕ} (hn : 2≤n) :
    ThresholdFourThirds.Bound (n : ℤ) (ThresholdFourThirds.excess intMinimum n) :=
  ThresholdFourThirds.uniform_squared intMinimum (by exact_mod_cast base_one) (minimum_step step) hn

theorem minimum_real (step : NativeStep) {n : ℕ} (hn : 2≤n) :
    2*(n : ℝ)+(4/3 : ℝ)*Real.sqrt ((n : ℝ)+3)-6 ≤ (minimum n : ℝ) := by
  simpa [intMinimum] using
    ThresholdFourThirds.uniform_real intMinimum (by exact_mod_cast base_one) (minimum_step step) hn

end ThresholdPublicMinimum
