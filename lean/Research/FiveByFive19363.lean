import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19363
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
    ⟨.or, [0, 6]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [1, 11]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.not, [15]⟩,
    ⟨.and, [12, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_19363

theorem PEqualNP.Outside.L_meta_19363 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3247934 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19363.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19363.witness]
  · decide
  · decide
