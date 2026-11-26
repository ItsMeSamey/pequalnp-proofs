import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19364
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.not, [14]⟩,
    ⟨.and, [12, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_19364

theorem PEqualNP.Outside.L_meta_19364 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576638 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19364.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19364.witness]
  · decide
  · decide
