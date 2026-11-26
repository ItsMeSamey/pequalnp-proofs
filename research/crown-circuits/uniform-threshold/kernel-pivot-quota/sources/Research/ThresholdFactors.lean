import Mathlib.Data.Finset.Card

namespace ThresholdFactors

/-- An input is represented by its true coordinates. -/
def Two {α : Type*} (x : Finset α) : Prop := 2 ≤ x.card

/-- Identifying the two copies of every label turns any monotone extension
of the promised bipartite crown into the full threshold-two predicate. -/
theorem identify {α : Type*} [DecidableEq α] [Nonempty α]
    (f : Finset α → Finset α → Prop)
    (mono : ∀ {a b c d}, a ⊆ b → c ⊆ d → f a c → f b d)
    (crown : ∀ i j, f {i} {j} ↔ i ≠ j) (x : Finset α) :
    f x x ↔ Two x := by
  classical
  constructor
  · intro h
    by_contra hsmall
    have hle : x.card ≤ 1 := by unfold Two at hsmall; omega
    obtain hx | ⟨i, hi⟩ := x.eq_empty_or_nonempty
    · subst x
      let i := Classical.choice (inferInstance : Nonempty α)
      exact (crown i i).mp (mono (Finset.empty_subset _) (Finset.empty_subset _) h) rfl
    · have heq : x = {i} := Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hi)
        (by simpa using hle) |>.symm
      subst x
      exact (crown i i).mp h rfl
  · intro h
    obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp (by unfold Two at h; omega : 1 < x.card)
    exact mono (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_subset_iff.mpr hj)
      ((crown i j).mpr hne)

/-- A detector with access to the two distinguished variables solely through their
disjunction cannot compute threshold two, even with arbitrary postprocessing. -/
theorem merged_or_obstruction {α : Type*} [DecidableEq α] (i j : α) (h : i ≠ j)
    (post : Bool → Finset α → Prop) :
    ¬ ∀ x : Finset α, Two x ↔ post (decide (i ∈ x ∨ j ∈ x)) (x \ {i,j}) := by
  intro repr
  have a := repr {i}
  have b := repr {i,j}
  have sub : ({i} : Finset α) \ {i,j} = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (by simp)
  simp [Two,sub] at a
  simp [Two,h] at b
  exact a (by simpa using b)

end ThresholdFactors
