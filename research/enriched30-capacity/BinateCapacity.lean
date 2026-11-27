import BinateFirstFork
import PhysicalExceptionalPrefix

namespace SignedTrace
open PEqualNP.CircuitLowerBounds Gates Physical
open PhysicalExceptional

/-- Distinct first-fork producers of physically binate, odd-prefix raw donors.
The set is formed from all raw coordinates of the given circuit. -/
noncomputable def exceptionalForks (C : Circuit) (n : Nat) : Finset Nat := by
  classical
  exact ((Finset.range n).filter (fun d =>
    BinateDonor C n d ∧ prefixSign (LiveUses.firstFork C n d) false = true)).image
    (firstStop C n)

private theorem stop_agrees {f : Nat → List ActualUses.Use} {w : Nat}
    (walk : ForkWalk.Walk f w) : stopWire walk = stop walk := by
  induction walk <;> simp_all [stopWire, stop]

/-- For the original evaluated gate list, on any pair of rising and falling
one-coordinate edges, the donor's deterministic first stop has at least two
live incidences. Odd-prefix first stops occupy at most N-1 groups, where N
counts only NOT gates that can reach this circuit's designated output. -/
theorem binate_firstFork_capacity (C : Circuit) (n : Nat)
    (good : ∀ g ∈ C.gates, Good g) :
    (∀ d, BinateDonor C n d →
      2 ≤ (LiveUses.outgoing C n (firstStop C n d)).length) ∧
    (exceptionalForks C n).card ≤ (inverters C n).card - 1 := by
  classical
  constructor
  · intro d hb
    simpa only [firstStop, ← stop_agrees] using binate_firstFork C n d good hb
  · apply physical_exceptional_card
    intro g hg
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨_, hb, hp⟩ := Finset.mem_filter.mp hd
    obtain ⟨⟨_, _, xs, _, _, _, hx⟩, ⟨_, _, ys, _, _, _, hy⟩⟩ :=
      binate_with_pins C n d good hb
    exact ⟨d, xs, ys, rfl, hx, hy, hp⟩

end SignedTrace
