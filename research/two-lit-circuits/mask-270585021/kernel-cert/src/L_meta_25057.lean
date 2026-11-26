import Root25057
import N25057Result

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_25057 :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k=i ∨ k=j)) =
        (270585021 : ℕ).testBit (6*min i.val j.val+max i.val j.val) := by
  apply Probe25057.refute_of_ledger Numeric25057.allRows
  intro t ht
  interval_cases t
  · exact ⟨_,Numeric25057.root0⟩
  · exact ⟨_,Numeric25057.root1⟩
  · exact ⟨_,Numeric25057.root2⟩
  · exact ⟨_,Numeric25057.root3⟩
  · exact ⟨_,Numeric25057.root4⟩
