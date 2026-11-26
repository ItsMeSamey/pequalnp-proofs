import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Research.MissingCell

/-- For a silent raw, eleven neighbors must be covered. A singly charged AND
can supply eight, and a doubly charged AND can supply only one. -/
theorem silent_row_charge (a b : ℕ) (neighbors : 11 ≤ 8*a+b) : 4 ≤ 2*a+b := by
  omega

/-- Each silent raw requires two distinct AND gates on average, counting the
possibility that the two inputs of an AND copy different silent raws. -/
theorem silent_incidence_lower {ρ γ : Type*} (R : Finset ρ) (G : Finset γ)
    (both : γ → Bool) (hit : ρ → γ → Bool)
    (neighbors : ∀ r ∈ R, 11 ≤ 8*(G.filter (fun g => hit r g && !both g)).card
      + (G.filter (fun g => hit r g && both g)).card)
    (capacity : ∀ g ∈ G, (R.filter (fun r => hit r g)).card ≤ if both g then 2 else 1) :
    2*R.card ≤ G.card := by
  classical
  let charge (r : ρ) (g : γ) : ℕ :=
    2 * (if (hit r g && !both g) then 1 else 0) + (if (hit r g && both g) then 1 else 0)
  have row (r) (hr : r ∈ R) : 4 ≤ ∑ g ∈ G, charge r g := by
    simp only [charge,Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
    exact silent_row_charge _ _ (neighbors r hr)
  have col (g) (hg : g ∈ G) : ∑ r ∈ R, charge r g ≤ 2 := by
    have hc := capacity g hg
    simp only [charge,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_boole,Nat.cast_id]
    cases h : both g <;> simp [h] at hc ⊢ <;> omega
  have lo := Finset.sum_le_sum row
  have hi := Finset.sum_le_sum col
  rw [Finset.sum_comm] at lo
  simp only [Finset.sum_const] at lo hi
  change R.card * 4 ≤ _ at lo
  change _ ≤ G.card * 2 at hi
  omega

/-- Count a covered set of opposite singleton neighbors by the capacities of
the incident AND gates. Repeated coverage is permitted. -/
theorem silent_neighbor_cover {γ ν : Type*} [DecidableEq ν]
    (G : Finset γ) (N : Finset ν) (both hit : γ → Bool) (reach : γ → Finset ν)
    (cover : ∀ j ∈ N, ∃ g ∈ G, hit g = true ∧ j ∈ reach g)
    (cap : ∀ g ∈ G, hit g = true → (reach g).card ≤ if both g then 1 else 8) :
    N.card ≤ 8*(G.filter (fun g => hit g && !both g)).card +
      (G.filter (fun g => hit g && both g)).card := by
  classical
  let D (g : γ) := if hit g then reach g else ∅
  have sub : N ⊆ G.biUnion D := by
    intro j hj
    obtain ⟨g,hg,h,jm⟩ := cover j hj
    exact Finset.mem_biUnion.mpr ⟨g,hg,by simpa [D,h] using jm⟩
  have upper (g) (hg : g ∈ G) : (D g).card ≤
      8*(if hit g && !both g then 1 else 0) + (if hit g && both g then 1 else 0) := by
    cases hh : hit g
    · simp [D,hh]
    · have h := cap g hg hh
      cases hb : both g <;> simp [D,hh,hb] at h ⊢ <;> exact h
  have bound := (Finset.card_le_card sub).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum upper))
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_boole,Nat.cast_id] using bound

end PEqualNP.Research.MissingCell
