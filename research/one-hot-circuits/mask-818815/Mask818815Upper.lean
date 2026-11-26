import PEqualNP.Defs

namespace Mask818815
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
    ⟨.or, [7, 8]⟩,
    ⟨.or, [10, 9]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [13, 5]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [16, 15]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [18, 17]⟩], 19⟩

theorem upper : RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) =>
    (818815 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Monotone2, witness]
  · decide
  · decide

end Mask818815
