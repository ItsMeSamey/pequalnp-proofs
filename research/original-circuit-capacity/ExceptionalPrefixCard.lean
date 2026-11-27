import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

namespace ForkCertificates

variable {Vertex Group : Type*} [DecidableEq Vertex] [DecidableEq Group]

/-- A vertex in each exceptional group's prefix maps to that group under
`stop`. If none of the witnesses needs `last`, there are at most |inverters|−1
exceptional groups. Several groups need not be assigned witnesses in advance. -/
theorem card_le_erase_image_of_prefix_witness
    (exceptional : Finset Group) (inverters : Finset Vertex)
    (stop : Vertex → Group) (last : Vertex) (hlast : last ∈ inverters)
    (hw : ∀ g ∈ exceptional, ∃ a ∈ inverters, a ≠ last ∧ stop a = g) :
    exceptional.card ≤ inverters.card - 1 := by
  have hsub : exceptional ⊆ (inverters.erase last).image stop := by
    intro g hg
    obtain ⟨a, ha, hne, hstop⟩ := hw g hg
    exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hne, ha⟩, hstop⟩
  calc
    exceptional.card ≤ ((inverters.erase last).image stop).card :=
      Finset.card_le_card hsub
    _ ≤ (inverters.erase last).card := by apply Finset.card_image_le
    _ = inverters.card - 1 := Finset.card_erase_of_mem hlast

/-- The graph-facing bridge: for every exceptional group, produce a prefix
inverter `a` that stops at its branch and an inverter `b` of strictly larger
topological rank. The sets may be empty; subtraction is in ℕ. -/
theorem exceptional_card_le_inverter_card_sub_one
    (exceptional : Finset Group) (inverters : Finset Vertex)
    (rank : Vertex → ℕ) (stop : Vertex → Group)
    (hw : ∀ g ∈ exceptional, ∃ a ∈ inverters, stop a = g ∧
      ∃ b ∈ inverters, rank a < rank b) :
    exceptional.card ≤ inverters.card - 1 := by
  classical
  by_cases hI : inverters.Nonempty
  · obtain ⟨last, hlast, hmax⟩ := Finset.exists_max_image inverters rank hI
    apply card_le_erase_image_of_prefix_witness exceptional inverters stop last hlast
    intro g hg
    obtain ⟨a, ha, hstop, b, hb, hab⟩ := hw g hg
    refine ⟨a, ha, ?_, hstop⟩
    intro heq
    subst a
    exact (not_lt_of_ge (hmax b hb)) hab
  · have hempty : exceptional = ∅ := by
      ext g
      constructor
      · intro hg
        obtain ⟨a, ha, _⟩ := hw g hg
        exact (hI ⟨a, ha⟩).elim
      · simp
    simp [hempty]

end ForkCertificates
