import Research.CrownSilentReach
import Research.CrownSilentDeleted

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

/-- A size-40 crown representation with precisely 24 OR gates has at most six
raw singleton assignments on which every OR gate is false. -/
theorem crown_twenty_four_silent_le_six (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length = 24) :
    (Finset.univ.filter (fun r : Fin 24 =>
      (trueOrFlags C.gates (singleInput r)).count true = 0)).card ≤ 6 := by
  let R := Finset.univ.filter (fun r : Fin 24 => (trueOrFlags C.gates (singleInput r)).count true = 0)
  have sil (r : Fin 24) (hr : r ∈ R) := (Finset.mem_filter.mp hr).2
  apply six_of_silent_incidence C hm rep size ors.ge R sil
  have bound := silent_incidence_lower R (silentGates C R) (silentBoth C R) (silentIncident C)
    (silent_physical_row C hm rep ors.le R sil)
    (silent_column_capacity C R (fun r hr => rawSupport_eq_singleton C hm r (sil r hr)))
  exact bound.trans (Finset.card_le_card (silent_gate_deleted C R))
end PEqualNP.Research.MissingCell
