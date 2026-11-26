import PEqualNP.Defs

namespace PEqualNP.Outside.Control25057
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.not, [14]⟩], 15⟩

end PEqualNP.Outside.Control25057

theorem PEqualNP.Outside.Control25057 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (270585021 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.Control25057.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo,PEqualNP.Outside.Control25057.witness]
  · decide
  · decide
