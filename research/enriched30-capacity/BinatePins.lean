import SignedPhysicalPath

namespace SignedTrace.Physical
open SignedTrace.Gates PEqualNP.CircuitLowerBounds

/-- Assignments of width n differing only by raising donor d. -/
structure DonorFlip (n d : Nat) (lo hi : List Bool) : Prop where
  lowLength : lo.length = n
  highLength : hi.length = n
  lowBit : lo.getD d false = false
  highBit : hi.getD d false = true
  agree : ∀ i, i ≠ d → lo.getD i false = hi.getD i false

def BinateDonor (C : Circuit) (n d : Nat) : Prop :=
  (∃ lo hi, DonorFlip n d lo hi ∧ C.eval lo = false ∧ C.eval hi = true) ∧
  (∃ lo hi, DonorFlip n d lo hi ∧ C.eval lo = true ∧ C.eval hi = false)

theorem binate_with_pins (C : Circuit) (n d : Nat) (hg : ∀ g ∈ C.gates, Good g)
    (hb : BinateDonor C n d) :
    (∃ lo hi hops, DonorFlip n d lo hi ∧ C.eval lo = false ∧ C.eval hi = true ∧
      certificate C n d false hops) ∧
    (∃ lo hi hops, DonorFlip n d lo hi ∧ C.eval lo = true ∧ C.eval hi = false ∧
      certificate C n d true hops) := by
  obtain ⟨⟨lo, hi, hf, hl, hh⟩, ⟨lo', hi', hf', hl', hh'⟩⟩ := hb
  constructor
  · obtain ⟨i, hops, h⟩ := trace_with_pins C hi lo
      (hf.lowLength.trans hf.highLength.symm) hg hh hl
    have hid : i = d := by
      by_contra hn
      have he := hf.agree i hn
      rcases h with ⟨_, ht, hf0⟩ | ⟨_, hf0, ht⟩ <;> simp_all
    subst i
    rcases h with ⟨hp, _, _⟩ | ⟨_, hbad, _⟩
    · exact ⟨lo, hi, hops, hf, hl, hh, hf.highLength ▸ hp⟩
    · cases hf.highBit.symm.trans hbad
  · obtain ⟨i, hops, h⟩ := trace_with_pins C lo' hi'
      (hf'.highLength.trans hf'.lowLength.symm) hg hl' hh'
    have hid : i = d := by
      by_contra hn
      have he := hf'.agree i hn
      rcases h with ⟨_, ht, hf0⟩ | ⟨_, hf0, ht⟩ <;> simp_all
    subst i
    rcases h with ⟨_, hbad, _⟩ | ⟨hp, _, _⟩
    · cases hf'.lowBit.symm.trans hbad
    · exact ⟨lo', hi', hops, hf', hl', hh', hf'.lowLength ▸ hp⟩

end SignedTrace.Physical
