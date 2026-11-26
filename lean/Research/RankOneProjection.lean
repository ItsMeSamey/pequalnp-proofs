import Mathlib.Data.Fintype.Card

namespace RankOneProjection

/-- Nonzero latent forms in a rank-one clause all evaluate to the same bit u. -/
theorem rankOneClause {J : Type*} (j₀ : J) (u : Bool) (offset : J → Bool) :
    (∃ j, (u ^^ offset j) = true) ↔
      (∃ j, offset j ≠ offset j₀) ∨ (u ^^ offset j₀) = true := by
  constructor
  · rintro ⟨j, hj⟩
    by_cases h : offset j = offset j₀
    · exact Or.inr (h ▸ hj)
    · exact Or.inl ⟨j, h⟩
  · rintro (⟨j, h⟩ | h)
    · by_cases h₀ : (u ^^ offset j₀) = true
      · exact ⟨j₀, h₀⟩
      · refine ⟨j, ?_⟩
        cases u <;> cases hj : offset j <;> cases h₁ : offset j₀ <;> simp_all
    · exact ⟨j₀, h⟩

/-- O means an observed-only literal already holds at this observation. -/
theorem guardedEquation {J : Type*} (j₀ : J) (O : Prop) (u : Bool) (offset : J → Bool) :
    (O ∨ ∃ j, (u ^^ offset j) = true) ↔
      ((¬ O ∧ ∀ j, offset j = offset j₀) → (u ^^ offset j₀) = true) := by
  classical
  rw [rankOneClause j₀]
  constructor
  · rintro (hO | ⟨j, h⟩ | h) hguard
    · exact (hguard.1 hO).elim
    · exact (h (hguard.2 j)).elim
    · exact h
  · intro h
    by_cases hO : O
    · exact Or.inl hO
    · by_cases same : ∀ j, offset j = offset j₀
      · exact Or.inr (Or.inr (h ⟨hO, same⟩))
      · exact Or.inr (Or.inl (Classical.not_forall.mp same))

abbrev Triple := Bool × Bool × Bool

def hit (l : Triple) : Bool := l.1 || l.2.1 || l.2.2

def first (l : Triple) : Triple :=
  (l.1, (!l.1) && l.2.1, (!l.1) && (!l.2.1) && l.2.2)

def base (l s : Triple) : Prop :=
  (s.1 ^^ s.2.1 ^^ s.2.2) = true ∧
  (s.1 = true → l.1 = true) ∧
  (s.2.1 = true → l.2.1 = true) ∧
  (s.2.2 = true → l.2.2 = true)

def firstGadget (l s : Triple) : Prop :=
  base l s ∧
  (s.2.1 = true → l.1 = false) ∧
  (s.2.2 = true → l.1 = false) ∧
  (s.2.2 = true → l.2.1 = false)

instance (l s : Triple) : Decidable (base l s) := by unfold base; infer_instance
instance (l s : Triple) : Decidable (firstGadget l s) := by unfold firstGadget; infer_instance

theorem local_first (l s : Triple) :
    firstGadget l s ↔ hit l = true ∧ s = first l := by
  rcases l with ⟨a,b,c⟩
  rcases s with ⟨d,e,f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem local_base (l s : Triple) (h : base l s) : hit l = true := by
  rcases l with ⟨a,b,c⟩
  rcases s with ⟨d,e,f⟩
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem star_projection {I : Type*} (lit : I → Triple) :
    (∀ i, hit (lit i) = true) ↔ ∃ sigma : I → Triple, ∀ i, base (lit i) (sigma i) := by
  constructor
  · intro h
    exact ⟨fun i => first (lit i), fun i => ((local_first _ _).mpr ⟨h i, rfl⟩).1⟩
  · rintro ⟨sigma, h⟩ i
    exact local_base _ _ (h i)

theorem unique_projection {I : Type*} (lit : I → Triple) :
    (∀ i, hit (lit i) = true) ↔ ∃! sigma : I → Triple, ∀ i, firstGadget (lit i) (sigma i) := by
  constructor
  · intro h
    refine ⟨fun i => first (lit i), fun i => (local_first _ _).mpr ⟨h i, rfl⟩, ?_⟩
    intro other ho
    funext i
    exact ((local_first _ _).mp (ho i)).2
  · rintro ⟨sigma, h, _⟩ i
    exact ((local_first _ _).mp (h i)).1

end RankOneProjection
