import Research.CrownTriggerCapacity
import Research.AdjacentCrownCore

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem crown_no_adjacent_nontriangle (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b c : Fin C.gates.length} (ac : a ≠ c) (ab : a ≠ b) (bc : b ≠ c)
    (eab : shareOrRead C a b) (ebc : shareOrRead C b c) (eac : ¬shareOrRead C a c) : False := by
  obtain ⟨T,small,hit⟩ := adjacent_trigger_container C hm rep ors ac ab bc eab ebc eac
  have large := crown_trigger_capacity C hm rep size ors T hit
  omega

end PEqualNP.Research.MissingCell
