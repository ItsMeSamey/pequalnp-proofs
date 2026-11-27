import Enriched30Data
import Enriched30Retained

namespace Enriched30RetainedBinding

def sourcePrefixRows : List Enriched30Retained.Row :=
  (((Enriched30Data.circuit.gates.take 156).zipIdx.map
    (fun e => (64 + e.2, e.1.inputs)))).reverse

set_option maxRecDepth 65536 in
theorem prefixRows_eq :
    Enriched30Retained.prefixRows = sourcePrefixRows := by decide +kernel

theorem bank_eq : Enriched30Retained.bank = Enriched30Data.bank := by decide +kernel

/-- Address 69 is emitted by gate index 5 and reads address 68. -/
theorem marker_opcode :
    (Enriched30Data.circuit.gates[5]?).map (fun g => g.op) = some .not := by rfl

theorem marker_operand :
    (Enriched30Data.circuit.gates[5]?).map (fun g => g.inputs) = some [68] := by rfl

theorem source_attached_price (paid liveSlots : Finset Nat)
    (pivotal : Enriched30Retained.mandatorySlots ⊆ liveSlots)
    (attach : ∀ j ∈ liveSlots, 64 ≤ Enriched30Data.bank.getD j 0 →
      Enriched30Data.bank.getD j 0 ∈ paid)
    (anchor : 69 ∈ paid)
    (closed : Enriched30Retained.ProducerClosed sourcePrefixRows paid) : 154 ≤ paid.card :=
  Enriched30Retained.retained_of_attached_slots paid liveSlots pivotal
    (by simpa only [bank_eq] using attach) anchor
    (by simpa only [prefixRows_eq] using closed)

end Enriched30RetainedBinding
