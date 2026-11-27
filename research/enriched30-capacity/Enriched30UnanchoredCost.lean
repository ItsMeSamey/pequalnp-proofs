import Enriched30ActualCost

namespace Enriched30ActualCost
open PEqualNP.CircuitLowerBounds SignedTrace
open ScalarFork.PhysicalLiveIncidence
open scoped BigOperators

/-- Producer cone seeded by the gate-valued bank wires used by the live decoder. -/
noncomputable def actualUnanchored (C : Circuit) : Finset Nat :=
  Enriched30Retained.scan Enriched30RetainedBinding.sourcePrefixRows (actualRoots C)

theorem unanchored_producer_floor (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (realizes : Enriched30Candidate.Realizes C) : 153 ≤ (actualUnanchored C).card := by
  rw [← Enriched30Retained.requiredOnly_card]
  unfold actualUnanchored Enriched30Retained.requiredOnly
  rw [← Enriched30RetainedBinding.prefixRows_eq]
  exact Finset.card_le_card (scan_mono _ (mandatory_subset C good realizes))

theorem unanchored_physical_live_floor (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (realizes : Enriched30Candidate.Realizes C) :
    182 ≤ (actualUnanchored C).card +
      ((∑ w ∈ vertices C 30, binCharge C 30 w) + (PhysicalExceptional.inverters C 30).card) :=
  Nat.add_le_add (unanchored_producer_floor C good realizes) (tail_live_floor C good cap realizes)

theorem unanchored_physical_size_floor (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (realizes : Enriched30Candidate.Realizes C) :
    182 ≤ (actualUnanchored C).card + C.size :=
  (unanchored_physical_live_floor C good cap realizes).trans
    (Nat.add_le_add_left (live_charge_le_size C 30) _)

end Enriched30ActualCost
