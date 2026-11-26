import ThresholdUpperLedger
import ThresholdUpperMonotone
import ThresholdPublicMinimum

namespace ThresholdThreeLayerUpper
open T2SoleOrSplice

theorem computes {n v w z : Nat} (L : Layers n v w z) : Computes n (circuit L) := by
  intro s
  have eq : activeInputs n (vector s) = s := by
    ext i
    simp [activeInputs,vector,List.getD_eq_getElem?_getD]
  rw [circuit_eval L (vector s) (by simp [vector]),eq]
  simp

theorem public_upper {n v w z : Nat} (L : Layers n v w z) :
    ThresholdPublicMinimum.minimum n ≤ 2*n+v+w+16*z :=
  (ThresholdPublicMinimum.le_size (monotone2 L) (computes L)).trans (physical_budget L)
end ThresholdThreeLayerUpper
