import BinateCapacity
import OutgoingPins
import LiveUsesIncidenceBridge

namespace SignedTrace
open PEqualNP.CircuitLowerBounds Physical PhysicalExceptional
open ScalarFork.PhysicalLiveIncidence
open scoped BigOperators

/-- Distinct canonical stop wires occupied by a semantically binate raw donor. -/
noncomputable def occupiedForks (C : Circuit) (n : Nat) : Finset Nat := by
  classical
  exact ((Finset.range n).filter (BinateDonor C n)).image (firstStop C n)

/-- Two capacities on the actual designated output of a finite signed circuit.
All sets are defined from the original gate list and its evaluation, including
the sets of raw donors and output-live NOT gates. Parallel pins count as uses. -/
theorem original_circuit_capacity (C : Circuit) (n : Nat)
    (good : ∀ g ∈ C.gates, Gates.Good g)
    (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ((vertices C n).filter (fun w => w < n)).card + (occupiedForks C n).card ≤
      (∑ w ∈ vertices C n, binCharge C n w) + 1 ∧
    (exceptionalForks C n).card ≤ (inverters C n).card - 1 := by
  classical
  obtain ⟨hstop, hex⟩ := binate_firstFork_capacity C n good
  refine ⟨canonical_capacity C n (occupiedForks C n) cap ?_, hex⟩
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
  exact OutgoingPins.two_pins (hstop d (Finset.mem_filter.mp hd).2)

end SignedTrace
