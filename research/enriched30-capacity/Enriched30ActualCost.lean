import Enriched30RetainedBinding
import Enriched30Candidate
import BinateInverterCharge
import LiveChargeSize

namespace Enriched30ActualCost
open PEqualNP.CircuitLowerBounds SignedTrace
open ScalarFork.PhysicalLiveIncidence
open scoped BigOperators

noncomputable def sourceSlots (C : Circuit) := (vertices C 30).filter (fun w => w < 30)

noncomputable def actualRoots (C : Circuit) : Finset Nat :=
  ((sourceSlots C).image (fun i => Enriched30Pivot.bank.getD i 0)).filter (fun w => 64 ≤ w)

noncomputable def actualRetained (C : Circuit) : Finset Nat :=
  Enriched30Retained.scan Enriched30RetainedBinding.sourcePrefixRows (insert 69 (actualRoots C))

theorem scan_mono (rows : List Enriched30Retained.Row) {s t : Finset Nat}
    (st : s ⊆ t) : Enriched30Retained.scan rows s ⊆ Enriched30Retained.scan rows t := by
  induction rows generalizing s t with
  | nil => exact st
  | cons r rs ih =>
    apply ih
    by_cases hs : r.1 ∈ s
    · have ht := st hs
      simp only [Enriched30Retained.addPins,hs,ht,if_true]
      intro x hx
      rcases Finset.mem_union.mp hx with a|b
      · exact Finset.mem_union_left _ a
      · exact Finset.mem_union_right _ (st b)
    · by_cases ht : r.1 ∈ t
      · simp only [Enriched30Retained.addPins,hs,ht,if_false,if_true]
        exact st.trans Finset.subset_union_right
      · simpa [Enriched30Retained.addPins,hs,ht] using st

private theorem mandatory_binding :
    Enriched30Retained.mandatoryWires = Enriched30Pivot.mandatoryWires := by decide +kernel

theorem mandatory_subset (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (realizes : Enriched30Candidate.Realizes C) :
    Enriched30Retained.requiredRoots ⊆ actualRoots C := by
  intro w hw
  obtain ⟨hm, paid⟩ := Finset.mem_filter.mp hw
  rw [mandatory_binding] at hm
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
    ⟨i,Enriched30Candidate.mandatory_mem C good realizes i hi,rfl⟩,paid⟩

set_option maxRecDepth 65536 in
theorem producer_floor (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (realizes : Enriched30Candidate.Realizes C) : 154 ≤ (actualRetained C).card := by
  rw [←Enriched30Retained.requiredWithAnchor_card]
  unfold actualRetained Enriched30Retained.requiredWithAnchor
  rw [←Enriched30RetainedBinding.prefixRows_eq]
  exact Finset.card_le_card (scan_mono Enriched30Retained.prefixRows
    (Finset.insert_subset_insert 69 (mandatory_subset C good realizes)))

theorem tail_live_floor (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (realizes : Enriched30Candidate.Realizes C) :
    29 ≤ (∑ w ∈ vertices C 30, binCharge C 30 w) + (PhysicalExceptional.inverters C 30).card := by
  have mandatory : Enriched30Pivot.mandatory ⊆ sourceSlots C :=
    fun i hi => Enriched30Candidate.mandatory_mem C good realizes i hi
  have count := Finset.card_le_card mandatory
  rw [Enriched30Pivot.mandatory_card] at count
  have cost := binate_sources_succ_le_binary_add_inverters C 30 2 good cap (by decide)
    (Enriched30Candidate.realizes_binate C realizes)
  change 28 ≤ ((vertices C 30).filter (fun w => w < 30)).card at count
  omega

theorem physical_live_floor (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (realizes : Enriched30Candidate.Realizes C) :
    183 ≤ (actualRetained C).card +
      ((∑ w ∈ vertices C 30, binCharge C 30 w) + (PhysicalExceptional.inverters C 30).card) :=
  Nat.add_le_add (producer_floor C good realizes) (tail_live_floor C good cap realizes)

theorem physical_size_floor (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (realizes : Enriched30Candidate.Realizes C) :
    183 ≤ (actualRetained C).card + C.size :=
  (physical_live_floor C good cap realizes).trans
    (Nat.add_le_add_left (live_charge_le_size C 30) _)

end Enriched30ActualCost
