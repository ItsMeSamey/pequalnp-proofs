import Research.CrownNoOrCollision
import Research.CrownSharedLabelBound
import Research.CrownNestedAdjustment
import Research.CrownLabelExcessBridge
import Research.CrownExcessObstruction

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open scoped BigOperators

/-- A size-forty monotone fan-in-two representation of the twelve-label crown
uses at least twenty-four OR gates. The bound concerns the one-each promise. -/
theorem crown_size_forty_requires_twenty_four_ors (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun i j : Fin 12 => decide (i ≠ j)) C)
    (size : C.size ≤ 40) : 24 ≤ (C.gates.filter isOrGate).length := by
  by_contra! below
  have ors : (C.gates.filter isOrGate).length ≤ 23 := by omega
  obtain ⟨D,dm,dr,do_,ds,mini⟩ := choose_crown_minimal C hm rep ors
  have cap : D.size ≤ 40 := ds.trans size
  have noOverlap (a b : Fin D.gates.length) (ne : a ≠ b) :
      Disjoint (readAt D.gates 24 a.val) (readAt D.gates 24 b.val) := by
    apply Finset.disjoint_left.mpr
    intro x ha hb
    exact crown_no_or_collision D dm dr cap do_ ne ⟨x,ha,hb⟩
  have few := CrownLabels.physical_shared_card_le_three D dm dr mini cap do_
  obtain ⟨bad,paid,capacity⟩ :=
    CrownLabels.nested_weight_adjustment D dm dr mini cap do_ noOverlap
  have excess := CrownLabels.total_excess D dm dr do_ bad (by omega) paid
  exact crown_excess_obstruction D dm dr cap (CrownLabels.adjustedQuarter D bad)
    (CrownLabels.adjusted_pos D dm dr do_ bad) capacity ((by decide : 13 ≤ 14).trans excess)

/-- In particular a size-forty crown circuit can contain at most sixteen AND gates. -/
theorem crown_size_forty_at_most_sixteen_ands (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun i j : Fin 12 => decide (i ≠ j)) C)
    (size : C.size ≤ 40) : (C.gates.filter isAndGate).length ≤ 16 := by
  have h := crown_size_forty_requires_twenty_four_ors C hm rep size
  have p := and_or_partition C.gates (fun g hg => (hm g hg).1)
  change C.gates.length ≤ 40 at size
  omega

end PEqualNP.Research.MissingCell
