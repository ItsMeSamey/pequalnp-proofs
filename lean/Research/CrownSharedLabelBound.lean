import Research.CrownSharedFirstBound
import Research.CrownCircuitLabels

namespace PEqualNP.Research.MissingCell.CrownLabels
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open PEqualNP.Research.CrownIdentify

theorem physical_shared_card_le_three (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    (shared C).card ≤ 3 := by
  classical
  apply shared_first_card_le_three C hm rep mini size ors (shared C)
  intro i hi
  obtain ⟨ha,hb,eq⟩ := (Finset.mem_filter.mp hi).2
  exact sharedFirst_of_common_min C i (rowPort i) (colPort i) rfl rfl ha hb eq

end PEqualNP.Research.MissingCell.CrownLabels
