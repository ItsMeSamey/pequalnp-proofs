import PEqualNP.Defs

namespace PEqualNP.Outside.Control23724
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.not, [0]⟩,
  ⟨.and, [3, 5]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.and, [0, 7]⟩,
  ⟨.or, [4, 6]⟩,
  ⟨.or, [8, 9]⟩,
  ⟨.not, [10]⟩], 11⟩

end PEqualNP.Outside.Control23724

theorem PEqualNP.Outside.Control23724 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4297 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.Control23724.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.Control23724.witness]
  · decide
  · decide
