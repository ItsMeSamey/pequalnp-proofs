import Mathlib.Data.Finset.Card

namespace GateEliminationCost

/-- A cheap step saves one gate and every other step saves two. -/
theorem telescope (gates : ℕ → ℕ) (cheap : Finset ℕ) (d : ℕ)
    (step : ∀ i < d, gates (i+1) + (if i ∈ cheap then 1 else 2) ≤ gates i) :
    gates d + 2*d ≤ gates 0 + ((Finset.range d).filter (· ∈ cheap)).card := by
  induction d with
  | zero => simp
  | succ d ih =>
    have prev := ih (fun i hi => step i (by omega))
    have last := step d (by omega)
    have fresh : d ∉ (Finset.range d).filter (· ∈ cheap) := by simp
    by_cases hd : d ∈ cheap
    · simp [Finset.range_add_one, Finset.filter_insert, hd, fresh] at last ⊢
      omega
    · simp [Finset.range_add_one, Finset.filter_insert, hd] at last ⊢
      omega

/-- A packing bound on exceptional vertices jointly pays for all cheap
deletions and the isolated vertices of the final induced graph. -/
theorem packed_cost {α : Type*} [DecidableEq α]
    (vertices d : ℕ) (gates : ℕ → ℕ) (deleted : ℕ → α)
    (cheap : Finset ℕ) (isolated bad : Finset α)
    (step : ∀ i < d, gates (i+1) + (if i ∈ cheap then 1 else 2) ≤ gates i)
    (fresh : Set.InjOn deleted (↑(Finset.range d) : Set ℕ))
    (marked : ∀ i < d, i ∈ cheap → deleted i ∈ bad)
    (survived : ∀ i < d, deleted i ∉ isolated)
    (isolates_bad : isolated ⊆ bad)
    (support : vertices ≤ gates d + 1 + d + isolated.card) :
    vertices + d ≤ gates 0 + 1 + bad.card := by
  classical
  let C := (Finset.range d).filter (· ∈ cheap)
  have cc : (C.image deleted).card = C.card := Finset.card_image_of_injOn (by
    intro i hi j hj eq
    exact fresh (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 eq)
  have dis : Disjoint (C.image deleted) isolated := by
    apply Finset.disjoint_left.mpr
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact survived i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
  have sub : C.image deleted ∪ isolated ⊆ bad := by
    apply Finset.union_subset _ isolates_bad
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hi
    exact marked i (Finset.mem_range.mp h₁) h₂
  have pack := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis, cc] at pack
  have total := telescope gates cheap d step
  change gates d + 2*d ≤ gates 0 + C.card at total
  omega

end GateEliminationCost
