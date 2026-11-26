import ThresholdRegularThirdOrder
import ThresholdPhysicalReceiverPower
import ThresholdNativeRough
namespace ThresholdRegularThird
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity T2SoleOrSplice ThresholdThirdDeletion

theorem regular : RegularTenth := by
  apply regular_order
  intro n out gs hn minim reg t E sq cut exc small
  exact physical_power hn minim reg t E sq cut exc small
    (ThresholdNativeRough.rough hn minim reg t E sq cut exc small)
    (ThresholdPhysicalReceiverGraph.native_power minim reg (by omega))

theorem bound_power {n : Nat} (large : (2:Nat)^402≤n) (C : Circuit)
    (mono : Monotone2 C) (computes : Computes n C) :
    let z := (C.size:ℝ)-2*(n:ℝ)-Real.sqrt (2*(n:ℝ))
    0≤z ∧ (n:ℝ)^3≤((2:ℝ)^15*z)^10 :=
  circuit_tenth regular large C mono computes

#print axioms regular
#print axioms bound_power
end ThresholdRegularThird
