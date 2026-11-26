import PEqualNP.Defs

namespace PEqualNP.Outside.Control10
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
    ⟨.or, [4, 9]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.and, [10, 13]⟩,
    ⟨.or, [14, 0]⟩,
    ⟨.and, [15, 12]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.not, [17]⟩,
    ⟨.or, [18, 16]⟩], 19⟩

end PEqualNP.Outside.Control10

theorem PEqualNP.Outside.Control10 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents
        (fun u v : Fin 5 => (7879121 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.Control10.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.Control10.witness]
  · decide
  · decide
