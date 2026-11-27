import OriginalCircuitCapacity

namespace SignedTrace
open PEqualNP.CircuitLowerBounds Physical PhysicalExceptional
open ScalarFork.PhysicalLiveIncidence
open scoped BigOperators

/-- A sign change along an output-directed physical run traverses an actual
output-live NOT gate. This lemma counts the destination of each operand hop. -/
theorem signed_run_inverters_nonempty {C : Circuit} {n w : Nat} {s t : Bool}
    {xs : List FirstDivergence.Hop}
    (hr : FirstDivergence.Run C n w s C.output t xs) (hne : s ≠ t) :
    (inverters C n).Nonempty := by
  classical
  induction xs generalizing w s with
  | nil => exact (hne hr.2).elim
  | cons h hs ih =>
    by_cases he : FirstDivergence.nextSign C n h s = s
    · exact ih hr.2 (by simpa [he] using hne)
    · obtain ⟨hn, _, g, hg, _, _⟩ := hr.1
      have bound := (List.getElem?_eq_some_iff.mp hg).choose
      have hop : g.op = .not := by
        cases op : g.op <;> simp_all [FirstDivergence.nextSign]
      exact ⟨h.1, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hn, LiveUses.run_live hr.2, by simp [hg,hop]⟩⟩

theorem binate_inverters_nonempty (C : Circuit) (n d : Nat)
    (good : ∀ g ∈ C.gates, Gates.Good g) (hb : BinateDonor C n d) :
    (inverters C n).Nonempty := by
  obtain ⟨_, ⟨_, _, hs, _, _, _, cert⟩⟩ := binate_with_pins C n d good hb
  exact signed_run_inverters_nonempty (FirstDivergence.certificate_walk cert) (by decide)

theorem binate_occupied_nonempty (C : Circuit) (n d : Nat) (hd : d < n)
    (hb : BinateDonor C n d) : (occupiedForks C n).Nonempty := by
  classical
  exact ⟨firstStop C n d, Finset.mem_image.mpr
    ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd,hb⟩,rfl⟩⟩

/-- One binate donor pays for one distinct first branch and one live NOT.
The incidences of the former are already counted by original_circuit_capacity. -/
theorem binate_sources_succ_le_binary_add_inverters (C : Circuit) (n d : Nat)
    (good : ∀ g ∈ C.gates, Gates.Good g) (cap : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : d < n) (hb : BinateDonor C n d) :
    ((vertices C n).filter (fun w => w < n)).card + 1 ≤
      (∑ w ∈ vertices C n, binCharge C n w) + (inverters C n).card := by
  classical
  have hc := (original_circuit_capacity C n good cap).1
  have hf := Finset.card_pos.mpr (binate_occupied_nonempty C n d hd hb)
  have hn := Finset.card_pos.mpr (binate_inverters_nonempty C n d good hb)
  omega

end SignedTrace
