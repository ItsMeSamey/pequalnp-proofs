import PEqualNP.Defs

namespace PEqualNP.Outside.Control24202
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or, [1, 2]⟩,
  ⟨.and, [6, 3]⟩,
  ⟨.or, [6, 3]⟩,
  ⟨.and, [4, 8]⟩,
  ⟨.or, [7, 9]⟩,
  ⟨.or, [5, 10]⟩,
  ⟨.not, [11]⟩], 12⟩

end PEqualNP.Outside.Control24202

theorem PEqualNP.Outside.Control24202 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.Control24202.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.Control24202.witness]
  · decide
  · decide
