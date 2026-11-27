import Signed9822Core
namespace Research.Signed9822
open PEqualNP.Outside.L_meta_9825.Engine
open PEqualNP.CircuitLowerBounds
theorem binaryFloor (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = predicate x) :
    15 ≤ C.gates.countP (fun g => !isNot g) :=
  binaryFloorOfFace h1015_14 C hf hc
theorem notBudget (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = predicate x) :
    15 + C.gates.countP isNot ≤ C.size :=
  notBudgetOfFace h1015_14 C hf hc
end Research.Signed9822
#print axioms Research.Signed9822.binaryFloor
