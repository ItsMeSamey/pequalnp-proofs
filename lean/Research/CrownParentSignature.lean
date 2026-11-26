import Research.CrownParentSignatureCore
import Research.CrownCommonParent

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem crown_parent_signature_equal (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (i j : Fin 12) (k : Fin C.gates.length) (a : ℕ) (read : a ∈ readAt C.gates 24 k.val)
    (ax : (C.wires (oneEach i i)).getD a false = true)
    (ay : (C.wires (oneEach j j)).getD a false = true) :
    trueOrFlags C.gates (oneEach i i) = trueOrFlags C.gates (oneEach j j) :=
  parent_signature_equal_of_overlap C hm rep ors (crown_common_parent C hm rep size ors) i j k a read ax ay

theorem crown_parent_positive_diagonals_le_two (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (k : Fin C.gates.length) (a : ℕ) (read : a ∈ readAt C.gates 24 k.val) :
    (Finset.univ.filter (fun i : Fin 12 => (C.wires (oneEach i i)).getD a false)).card ≤ 2 :=
  parent_diagonals_bound_of_overlap C hm rep size ors (crown_common_parent C hm rep size ors) k a read

theorem crown_or_positive_signatures_le_two (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) (k : Fin C.gates.length) :
    ((Finset.univ.filter (fun i : Fin 12 => k ∈ activeOrIds C.gates (oneEach i i))).image
      (fun i => trueOrFlags C.gates (oneEach i i))).card ≤ 2 :=
  gate_signatures_bound_of_overlap C hm rep ors (crown_common_parent C hm rep size ors) k

theorem crown_or_positive_diagonals_le_four (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (k : Fin C.gates.length) :
    (Finset.univ.filter (fun i : Fin 12 => k ∈ activeOrIds C.gates (oneEach i i))).card ≤ 4 :=
  gate_diagonals_bound_of_overlap C hm rep size ors (crown_common_parent C hm rep size ors) k

end PEqualNP.Research.MissingCell
