import Research.CrownDemandCap
import Research.CrownCollisionSaturationFive

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem crown_no_or_collision (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b : Fin C.gates.length} (ne : a ≠ b) : ¬shareOrRead C a b := by
  intro edge
  let sat := Finset.univ.filter (fun i : Fin 12 => 2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)
  have few : sat.card ≤ 5 := crown_collision_saturated_le_five C hm rep size ors ne edge
  apply CrownDemandArithmetic.exclude_collision (fun i => singletonExcess C (rowPort i))
    (fun i => singletonExcess C (colPort i)) sat few _ (crown_demand_cap C hm rep size ors)
  intro i hi
  apply unsaturated_label_excess C hm i
  by_contra! high
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)

end PEqualNP.Research.MissingCell
