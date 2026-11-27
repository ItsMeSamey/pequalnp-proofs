import Root24202
import N24202Result

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_24202 :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k=i ∨ k=j)) =
        (270549407 : ℕ).testBit (6*min i.val j.val+max i.val j.val) := by
  apply Probe24202.refute_of_ledger Numeric24202.allRows
  · intro t ht
    interval_cases t
    · exact ⟨_,Numeric24202.root3⟩
    · exact ⟨_,Numeric24202.root4⟩
  · intro t ht
    interval_cases t
    · exact ⟨_,Numeric24202.root0⟩
    · exact ⟨_,Numeric24202.root1⟩
    · exact ⟨_,Numeric24202.root2⟩
