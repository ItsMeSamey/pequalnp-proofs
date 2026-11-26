import Research.CrownFourOrSources
import Research.CrownCollisionUnique

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Every size-forty representation of the 12-crown using at most 23 OR
gates must feed at least 45 distinct wires to OR gates. At least four of
those wires are themselves OR outputs. -/
theorem crown_forty_five_wires_four_or_sources (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    45 ≤ (readUnion (orInputSets C.gates 24)).card ∧
    4 ≤ ((readUnion (orInputSets C.gates 24)) ∩ orOutputWires C.gates 24).card := by
  apply crown_four_or_sources_of_unique_collision C hm rep size ors
  intro a b c d ab cd p q
  exact crown_collision_unique C hm rep size ors ab cd (Finset.not_disjoint_iff.mp p) (Finset.not_disjoint_iff.mp q)

theorem crown_and_or_source_budget (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    21 ≤ (C.gates.filter CrownDiagonalCharge.isAndGate).length +
      ((readUnion (orInputSets C.gates 24)) ∩ orOutputWires C.gates 24).card := by
  have wire := (crown_forty_five_wires_four_or_sources C hm rep size ors).1
  have budget := or_input_source_budget C hm 24
  omega

theorem crown_and_or_source_budget_no_collision (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (zero : ∀ a b : Fin C.gates.length, a ≠ b →
      Disjoint (readAt C.gates 24 a.val) (readAt C.gates 24 b.val)) :
    22 ≤ (C.gates.filter CrownDiagonalCharge.isAndGate).length +
      ((readUnion (orInputSets C.gates 24)) ∩ orOutputWires C.gates 24).card := by
  have wire := (crown_five_or_sources_of_no_collision C hm rep size ors zero).1
  have budget := or_input_source_budget C hm 24
  omega

end PEqualNP.Research.MissingCell
