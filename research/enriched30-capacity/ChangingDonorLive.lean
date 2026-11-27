import LiveUsesIncidenceBridge
import BinatePins

namespace SignedTrace.LiveUses

open PEqualNP.CircuitLowerBounds SignedTrace.Gates SignedTrace.Physical

private theorem live_of_transition (C : Circuit) {n d : Nat} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n)
    (hg : ∀ g ∈ C.gates, Good g)
    (agree : ∀ i, i ≠ d → x.getD i false = y.getD i false)
    (onX : C.eval x = true) (offY : C.eval y = false) : Live C n d := by
  obtain ⟨i, hops, h⟩ := trace_with_pins C x y (hy.trans hx.symm) hg onX offY
  have eq : i = d := by
    by_contra hn
    have same := agree i hn
    rcases h with ⟨_, ht, hf⟩ | ⟨_, hf, ht⟩ <;> simp_all
  subst i
  rcases h with ⟨hp, _, _⟩ | ⟨hp, _, _⟩ <;>
    exact hx ▸ run_live (FirstDivergence.certificate_walk hp)

theorem changing_donor_live (C : Circuit) {n d : Nat} {lo hi : List Bool}
    (hg : ∀ g ∈ C.gates, Good g) (flip : DonorFlip n d lo hi)
    (changes : C.eval lo ≠ C.eval hi) : Live C n d := by
  cases hl : C.eval lo <;> cases hh : C.eval hi
  · exact (changes (hl.trans hh.symm)).elim
  · exact live_of_transition C flip.highLength flip.lowLength hg
      (fun i h => (flip.agree i h).symm) hh hl
  · exact live_of_transition C flip.lowLength flip.highLength hg flip.agree hl hh
  · exact (changes (hl.trans hh.symm)).elim

end SignedTrace.LiveUses

namespace ScalarFork.PhysicalLiveIncidence

open PEqualNP.CircuitLowerBounds SignedTrace

theorem changing_donor_mem (C : Circuit) {n d : Nat} {lo hi : List Bool}
    (hg : ∀ g ∈ C.gates, Gates.Good g) (flip : Physical.DonorFlip n d lo hi)
    (changes : C.eval lo ≠ C.eval hi) :
    d ∈ (vertices C n).filter (fun w => w < n) := by
  apply Finset.mem_filter.mpr
  refine ⟨canonical_vertices.mpr (LiveUses.changing_donor_live C hg flip changes), ?_⟩
  by_contra! bad
  have bound : hi.length ≤ d := flip.highLength.trans_le bad
  have hfalse := List.getD_eq_default hi false bound
  exact Bool.noConfusion (hfalse.symm.trans flip.highBit)

end ScalarFork.PhysicalLiveIncidence
