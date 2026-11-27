import Q1DoubleOneLeak

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

/-- An AW edge supported on two labeled Y vertices would either be a loop,
cross the two induced residuals, or duplicate one of the assigned Y edges. -/
theorem exclusive_external {V : Type*} (G : SimpleGraph V) (label : Pos → V)
    (fresh : V → V → Prop) (sound : ∀ a b, fresh a b → G.Adj a b)
    (induced : ∀ p q : Pos, p.1 ≠ q.1 → ¬ G.Adj (label p) (label q))
    (exclusive : ∀ i j : Bool, ¬ fresh (label (i,j)) (label (i,!j))) :
    ∀ p q, ¬ fresh (label p) (label q) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ edge
  by_cases h : i = k
  · subst k
    by_cases e : j = l
    · subst l
      exact G.irrefl (sound _ _ edge)
    · have hl : l = !j := by cases j <;> cases l <;> simp_all
      subst l
      exact exclusive i j edge
  · exact induced (i,j) (k,l) h (sound _ _ edge)

theorem three_shared_empty {V : Type*} (G : SimpleGraph V) (label : Pos → V)
    (fresh : V → V → Prop) (T : Finset Pattern) (inj : Function.Injective label)
    (sound : ∀ a b, fresh a b → G.Adj a b)
    (induced : ∀ p q : Pos, p.1 ≠ q.1 → ¬ G.Adj (label p) (label q))
    (exclusive : ∀ i j : Bool, ¬ fresh (label (i,j)) (label (i,!j)))
    (meet : ∀ a b, fresh a b → ∀ t ∈ T, inSlot label t a ∨ inSlot label t b)
    (ht : 3 ≤ T.card) : ¬ ∃ a b, fresh a b := by
  have triple : ∀ S : Finset Pattern, 3 ≤ S.card →
      ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c := by decide
  obtain ⟨t,ht',s,hs,u,hu,ts,tu,su⟩ := triple T ht
  rintro ⟨a,b,hab⟩
  exact three_shared_impossible inj (exclusive_external G label fresh sound induced exclusive)
    meet ht' hs hu ts tu su a b hab

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
