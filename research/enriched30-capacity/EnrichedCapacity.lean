import OriginalCircuitCapacity
import ChangingDonorLive
import Enriched30Candidate
import Enriched30RetainedBinding
import BinateInverterCharge
import LiveChargeSize

namespace SignedTrace.Enriched
open PEqualNP.CircuitLowerBounds SignedTrace.Physical
open ScalarFork.PhysicalLiveIncidence
open scoped BigOperators

/-- Physical incidence capacity specialized to a family of 28 essential
coordinates and a single semantically binate coordinate. -/
theorem capacity_of_witnesses (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (mandatory : Finset Nat) (count : mandatory.card = 28)
    (essential : ∀ d ∈ mandatory, ∃ lo hi, DonorFlip 30 d lo hi ∧ C.eval lo ≠ C.eval hi)
    (d : Fin 30) (binate : BinateDonor C 30 d.val) :
    28 ≤ ((vertices C 30).filter (fun w => w < 30)).card ∧
    1 ≤ (occupiedForks C 30).card ∧
    28 ≤ ∑ w ∈ vertices C 30, binCharge C 30 w := by
  classical
  have hsub : mandatory ⊆ (vertices C 30).filter (fun w => w < 30) := by
    intro i hi
    obtain ⟨lo, hi', flip, changes⟩ := essential i hi
    exact changing_donor_mem C good flip changes
  have hraw := Finset.card_le_card hsub
  rw [count] at hraw
  have hex : (occupiedForks C 30).Nonempty := by
    unfold occupiedForks
    exact ⟨_, Finset.mem_image.mpr ⟨d.val,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr d.isLt, binate⟩, rfl⟩⟩
  have hfork := Finset.card_pos.mpr hex
  have hcap := (original_circuit_capacity C 30 good cap).1
  exact ⟨hraw, by omega, by omega⟩

/-- Any signed fan-in-two tail realizing the bank labels needs 29 gates. -/
theorem enriched30_tail_size (C : Circuit)
    (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (realizes : Enriched30Candidate.Realizes C) : 29 ≤ C.size := by
  classical
  have hsub : Enriched30Pivot.mandatory ⊆
      (vertices C 30).filter (fun w => w < 30) :=
    fun _ hd => Enriched30Candidate.mandatory_mem C good realizes _ hd
  have hraw := Finset.card_le_card hsub
  rw [Enriched30Pivot.mandatory_card] at hraw
  have hcharges := binate_sources_succ_le_binary_add_inverters C 30 2 good cap
    (by decide) (Enriched30Candidate.realizes_binate C realizes)
  have hsize := live_charge_le_size C 30
  omega

private theorem mandatory_wires_agree :
    Enriched30Retained.mandatoryWires = Enriched30Pivot.mandatoryWires := by
  decide +kernel

/-- The charged cost counts retained prefix gates and appended tail gates
as separate physical gates. Each live bank slot is pinned to its original
wire in Enriched30Data.bank. Its gate producer and the transitive input
producers in the serialized source prefix are charged to paid. Wire 69
is the additional retained marker. -/
theorem enriched30_retained_marker_cost (C : Circuit) (paid : Finset Nat)
    (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (realizes : Enriched30Candidate.Realizes C)
    (paysLive : ∀ j, j < 30 → LiveUses.Live C 30 j →
      64 ≤ Enriched30Pivot.bank.getD j 0 → Enriched30Pivot.bank.getD j 0 ∈ paid)
    (retainsMarker : 69 ∈ paid)
    (closed : Enriched30Retained.ProducerClosed Enriched30RetainedBinding.sourcePrefixRows paid) :
    183 ≤ paid.card + C.size := by
  classical
  have slots : Enriched30Retained.mandatorySlots = Enriched30Pivot.mandatory := by decide +kernel
  have hpaid := Enriched30RetainedBinding.source_attached_price paid
    ((vertices C 30).filter (fun w => w < 30))
    (by rw [slots]; exact fun j hj => Enriched30Candidate.mandatory_mem C good realizes j hj)
    (by
      intro j hj
      obtain ⟨hv, hjlt⟩ := Finset.mem_filter.mp hj
      exact paysLive j hjlt (canonical_vertices.mp hv))
    retainsMarker closed
  have htail := enriched30_tail_size C good cap realizes
  omega

/-- The same pinned bank producers and serialized prefix closure cost at
least 153 prefix gates even without the marker requirement. -/
theorem enriched30_retained_cost (C : Circuit) (paid : Finset Nat)
    (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (realizes : Enriched30Candidate.Realizes C)
    (paysLive : ∀ j, j < 30 → LiveUses.Live C 30 j →
      64 ≤ Enriched30Pivot.bank.getD j 0 → Enriched30Pivot.bank.getD j 0 ∈ paid)
    (closed : Enriched30Retained.ProducerClosed Enriched30RetainedBinding.sourcePrefixRows paid) :
    182 ≤ paid.card + C.size := by
  classical
  have hm : ∀ w ∈ Enriched30Retained.mandatoryWires, 64 ≤ w → w ∈ paid := by
    intro w hw hgate
    rw [mandatory_wires_agree] at hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    exact paysLive j (Enriched30Pivot.mandatory_lt hj)
      (Enriched30Candidate.mandatory_live C good realizes j hj) hgate
  have hpaid := Enriched30Retained.retained_unanchored_card_le paid hm
    (by simpa only [Enriched30RetainedBinding.prefixRows_eq] using closed)
  have htail := enriched30_tail_size C good cap realizes
  omega

end SignedTrace.Enriched
