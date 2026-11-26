import Research.CrownProperOrReads
import Research.CrownStaticOrIds
import Research.CrownCopyOr
import Research.CrownSingleCollisionCount
import Research.CrownOrToOr

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

private theorem biUnion_in_static (gs : List Gate) (n : ℕ) :
    (staticOrIds gs).biUnion (fun a => readAt gs n a.val) ⊆ readUnion (orInputSets gs n) := by
  intro x hx
  obtain ⟨g,hg,gx⟩ := Finset.mem_biUnion.mp hx
  exact (readUnion_mem ..).mpr ⟨_,staticOrIds_reads gs n g hg,gx⟩

theorem crown_four_or_sources_of_unique_collision (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (uniq : ∀ a b c d : Fin C.gates.length, a ≠ b → c ≠ d →
      ¬ Disjoint (readAt C.gates 24 a.val) (readAt C.gates 24 b.val) →
      ¬ Disjoint (readAt C.gates 24 c.val) (readAt C.gates 24 d.val) →
      ({a,b} : Finset _) = {c,d}) :
    45 ≤ (readUnion (orInputSets C.gates 24)).card ∧
    4 ≤ ((readUnion (orInputSets C.gates 24)) ∩ orOutputWires C.gates 24).card := by
  let S := staticOrIds C.gates
  let P (a : Fin C.gates.length) := readAt C.gates 24 a.val
  have two (a : Fin C.gates.length) (ha : a ∈ S) : (P a).card = 2 :=
    crown_or_reads_exactly_two C hm rep size ors _ (staticOrIds_reads C.gates 24 a ha)
  have diff (a : Fin C.gates.length) (ha : a ∈ S) (b : Fin C.gates.length) (hb : b ∈ S)
      (ab : a ≠ b) : P a ≠ P b :=
    crown_or_reads_distinct_by_replacement C hm rep size ors a b ha hb ab
  have lower := single_collision_wire_count S P two diff
    (fun a _ b _ c _ d _ => uniq a b c d)
  have le : (S.biUnion P).card ≤ (readUnion (orInputSets C.gates 24)).card :=
    Finset.card_le_card (biUnion_in_static C.gates 24)
  have old := crown_size_forty_requires_twenty_three_ors C hm rep size
  have count : S.card = (C.gates.filter isOrGate).length := staticOrIds_card ..
  have cap := or_source_budget C hm rep size
  constructor <;> omega

theorem crown_five_or_sources_of_no_collision (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (zero : ∀ a b : Fin C.gates.length, a ≠ b →
      Disjoint (readAt C.gates 24 a.val) (readAt C.gates 24 b.val)) :
    46 ≤ (readUnion (orInputSets C.gates 24)).card ∧
    5 ≤ ((readUnion (orInputSets C.gates 24)) ∩ orOutputWires C.gates 24).card := by
  let S := staticOrIds C.gates
  let P (a : Fin C.gates.length) := readAt C.gates 24 a.val
  have two (a : Fin C.gates.length) (ha : a ∈ S) : (P a).card = 2 :=
    crown_or_reads_exactly_two C hm rep size ors _ (staticOrIds_reads C.gates 24 a ha)
  have sep : (S : Set (Fin C.gates.length)).PairwiseDisjoint P := fun a _ b _ ab => zero a b ab
  have val : (S.biUnion P).card = 2*S.card := by
    rw [Finset.card_biUnion sep]
    calc
      ∑ g ∈ S, (P g).card = ∑ _g ∈ S, 2 := Finset.sum_congr rfl two
      _ = _ := by simp [Nat.mul_comm]
  have le : (S.biUnion P).card ≤ (readUnion (orInputSets C.gates 24)).card :=
    Finset.card_le_card (biUnion_in_static C.gates 24)
  have old := crown_size_forty_requires_twenty_three_ors C hm rep size
  have count : S.card = (C.gates.filter isOrGate).length := staticOrIds_card ..
  have cap := or_source_budget C hm rep size
  constructor <;> omega

end PEqualNP.Research.MissingCell
