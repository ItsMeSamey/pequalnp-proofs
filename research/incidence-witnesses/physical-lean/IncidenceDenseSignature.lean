import Mathlib.Data.Finset.Card

namespace IncidenceDenseSignature
variable {α : Type*} [DecidableEq α]

abbrev Sig (α : Type*) := Option (Finset α)

def high (s : Sig α) (D : Finset α) : Prop :=
  match s with
  | none => True
  | some A => ¬ A ⊆ D

def valid (t : ℕ) (s : Sig α) : Prop :=
  match s with
  | none => True
  | some A => A.card ≤ t

def merge (t : ℕ) (a b : Sig α) : Sig α :=
  match a, b with
  | some A, some B => if (A ∪ B).card ≤ t then some (A ∪ B) else none
  | _, _ => none

theorem valid_merge (t : ℕ) (a b : Sig α) : valid t (merge t a b) := by
  cases a with
  | none => trivial
  | some A =>
    cases b with
    | none => trivial
    | some B => by_cases h : (A ∪ B).card ≤ t <;> simp [merge,h,valid]

theorem merge_high {t : ℕ} (a b : Sig α) (D : Finset α) (hD : D.card ≤ t) :
    high (merge t a b) D ↔ high a D ∨ high b D := by
  classical
  cases a with
  | none => simp [merge,high]
  | some A =>
    cases b with
    | none => simp [merge,high]
    | some B =>
      by_cases h : (A ∪ B).card ≤ t
      · simp only [merge, if_pos h, high, Finset.union_subset_iff]
        tauto
      · have nsub : ¬ (A ∪ B) ⊆ D := fun sub => h ((Finset.card_le_card sub).trans hD)
        rw [Finset.union_subset_iff] at nsub
        simp only [merge, if_neg h, high, true_iff]
        tauto

theorem eq_of_dense {t : ℕ} {a b : Sig α} (ha : valid t a) (hb : valid t b)
    (same : ∀ D : Finset α, D.card ≤ t → (high a D ↔ high b D)) : a = b := by
  classical
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some B =>
      have h := (same B hb).mp trivial
      exact False.elim (h (fun _ hx => hx))
  | some A =>
    cases b with
    | none =>
      have h := (same A ha).mpr trivial
      exact False.elim (h (fun _ hx => hx))
    | some B =>
      have ba : B ⊆ A := by
        by_contra h
        exact (same A ha).mpr h (fun _ hx => hx)
      have ab : A ⊆ B := by
        by_contra h
        exact (same B hb).mp h (fun _ hx => hx)
      exact congrArg some (Finset.Subset.antisymm ab ba)

def represented (t : ℕ) (v : Finset α → Prop) : Prop :=
  ∃ a : Sig α, valid t a ∧ ∀ D, D.card ≤ t → (v D ↔ high a D)

/-- Induction on topologically ordered wires. A private AND and a
    nonprivate AND with agreeing operands use the single-parent case. -/
theorem dag_signatures {t : ℕ} (v : ℕ → Finset α → Prop)
    (step : ∀ i, represented t (v i) ∨
      (∃ l < i, ∀ D : Finset α, D.card ≤ t → (v i D ↔ v l D)) ∨
      (∃ l < i, ∃ r < i, ∀ D : Finset α, D.card ≤ t →
          (v i D ↔ v l D ∨ v r D))) :
    ∀ i, represented t (v i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rcases step i with input | ⟨l,hl,copy⟩ | ⟨l,hl,r,hr,join⟩
    · exact input
    · obtain ⟨a,ha,eval⟩ := ih l hl
      exact ⟨a,ha,fun D hD => (copy D hD).trans (eval D hD)⟩
    · obtain ⟨a,ha,leval⟩ := ih l hl
      obtain ⟨b,hb,reval⟩ := ih r hr
      refine ⟨merge t a b,valid_merge t a b,?_⟩
      intro D hD
      exact (join D hD).trans ((or_congr (leval D hD) (reval D hD)).trans
        (merge_high a b D hD).symm)

end IncidenceDenseSignature
