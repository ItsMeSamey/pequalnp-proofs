import ThresholdUnrestrictedGraph
import ThresholdFourThirdsReal

namespace ThresholdPublicInduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity T2SoleOrSplice ThresholdFourThirds
open T2RegularOrDelete

theorem bound_mono {n s t : ℤ} (h : Bound n s) (st : s ≤ t) : Bound n t := by
  obtain ⟨hp,hs⟩ := h
  constructor
  · omega
  · nlinarith [mul_nonneg (show 0≤t-s by omega) (show 0≤t+s+12 by omega)]

theorem native_base (C : Circuit) (m : Monotone2 C) (h : Computes 2 C) : 1≤C.size := by
  obtain ⟨E,eligible,price⟩ := T2BenchmarkNormalize.canNormalize (by decide : 2≤2) C m h
  obtain ⟨j,_⟩ := T2BenchmarkNormalize.output_internal eligible
  have l := j.isLt
  change E.gates.length ≤ C.size at price
  omega

theorem induction_all
    (base : ∀ C : Circuit, Monotone2 C → Computes 2 C → 1≤C.size)
    (step : ∀ k, 2≤k → ∀ C : Circuit, Monotone2 C → Computes (k+1) C →
      Saving k C.size ∨ Bound ((k+1:Nat):ℤ) ((C.size:ℤ)-2*((k+1:Nat):ℤ)))
    {n : Nat} (hn : 2≤n) (C : Circuit) (mono : Monotone2 C) (full : Computes n C) :
    Bound (n:ℤ) ((C.size:ℤ)-2*(n:ℤ)) := by
  have aux (l : Nat) : ∀ E : Circuit, Monotone2 E → Computes (l+2) E →
      Bound ((l+2:Nat):ℤ) ((E.size:ℤ)-2*((l+2:Nat):ℤ)) := by
    induction l with
    | zero =>
      intro E em ec
      have h := base E em ec
      exact base_bound (by exact_mod_cast h)
    | succ l ih =>
      intro E em ec
      rcases step (l+2) (by omega) E em ec with ⟨F,fm,fc,price⟩ | h
      · have prev := ih F fm fc
        have cost : (F.size:ℤ)+3≤E.size := by exact_mod_cast price
        have target := deletion_step (s' := (E.size:ℤ)-2*((l+3:Nat):ℤ)) prev (by push_cast; omega)
        convert target using 1 <;> push_cast <;> ring
      · exact h
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_comm] using aux l C mono (by simpa only [Nat.add_comm] using full)

end ThresholdPublicInduction
