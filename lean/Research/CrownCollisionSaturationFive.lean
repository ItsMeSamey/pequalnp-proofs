import Research.CrownSingleShared
import Research.CrownParentSignature

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

/-- If two distinct ORs read a common wire, at most five diagonals are
saturated. The common parent accounts for at most one diagonal, and
each gate has at most one remaining read, accounting for at most two. -/
theorem crown_collision_saturated_le_five (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b : Fin C.gates.length} (ab : a ≠ b) (edge : shareOrRead C a b) :
    (Finset.univ.filter (fun i : Fin 12 => 2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)).card ≤ 5 := by
  apply crown_collision_saturated_aux C hm rep size ors ab edge
  exact crown_parent_positive_diagonals_le_two C hm rep size ors

end PEqualNP.Research.MissingCell
