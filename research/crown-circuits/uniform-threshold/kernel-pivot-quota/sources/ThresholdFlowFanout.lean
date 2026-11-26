import ThresholdSharedFlow
import Mathlib.Algebra.BigOperators.Fin
open PEqualNP.CircuitLowerBounds T2OrPartition ThresholdOrExtraction
namespace ThresholdSharedFlow
theorem fan_readers {C : Circuit} {n} (L : Layout C n) (a : Id C) :
    fan L a=(readers C (n+a.val)).length := by
  unfold fan readers
  rw [Fin.sum_univ_def,List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  rw [ThresholdOrExtraction.layout_inputs (L.atIndex i)]
  by_cases hl : L.left i=n+a.val <;> by_cases hr : L.right i=n+a.val <;>
    simp [slots,hl,hr]
end ThresholdSharedFlow
