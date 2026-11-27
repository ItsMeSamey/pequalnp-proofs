import Root23724
import N23724Result

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_23724 :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧
      ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k=i ∨ k=j)) =
        (4297 : ℕ).testBit (5*min i.val j.val+max i.val j.val) := by
  apply Probe23724.refute_of_ledger Numeric23724.allRows
  intro t ht
  interval_cases t
  · exact ⟨_,Numeric23724.root0⟩
  · exact ⟨_,Numeric23724.root1⟩
  · exact ⟨_,Numeric23724.root2⟩
