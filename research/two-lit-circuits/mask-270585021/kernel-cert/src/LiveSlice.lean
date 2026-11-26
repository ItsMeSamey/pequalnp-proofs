import FreshBuild
namespace ProbeFrontier
variable {α : Type} [Fintype α] [DecidableEq α]

inductive ExactOp : Finset (Mask α) → Bool → Mask α → Prop where
  | neg (a : Mask α) : ExactOp {a} true (fun p => !(a p))
  | conj (a b : Mask α) (hab : a ≠ b) : ExactOp {a,b} false (fun p => a p && b p)
  | disj (a b : Mask α) (hab : a ≠ b) : ExactOp {a,b} false (fun p => a p || b p)

inductive LiveSlice (target : Mask α) : ℕ → ℕ → Finset (Mask α) → Prop where
  | finish : LiveSlice target 0 0 {target}
  | step {b t : ℕ} {T P : Finset (Mask α)} {neg : Bool} {y : Mask α}
      (op : ExactOp P neg y) (hy : y ∈ T)
      (fresh : ¬available (T.erase y ∪ P) y) (rest : LiveSlice target b t T) :
      LiveSlice target (b + if neg then 0 else 1) (t + if neg then 1 else 0) (T.erase y ∪ P)

omit [DecidableEq α] in
theorem Build.slice {target : Mask α} {b t : ℕ} {A : Finset (Mask α)}
    (build : Build target b t A) :
    ∃ S ⊆ A, ∃ b' ≤ b, ∃ t' ≤ t, LiveSlice target b' t' S := by
  induction build with
  | finish A ht => exact ⟨{target}, by simpa using ht, 0, by simp, 0, by simp, .finish⟩
  | @step b t A neg y op fresh rest ih =>
    obtain ⟨T, hT, bb, hb, tt, ht, sl⟩ := ih
    by_cases hy : y ∈ T
    · obtain ⟨P, hP, fact⟩ : ∃ P ⊆ A, ExactOp P neg y := by
        cases op with
        | neg a ha => exact ⟨{a}, by simpa using ha, .neg a⟩
        | conj a b ha hb h => exact ⟨{a,b}, by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl|rfl <;> assumption, .conj a b h⟩
        | disj a b ha hb h => exact ⟨{a,b}, by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl|rfl <;> assumption, .disj a b h⟩
      have sub : T.erase y ∪ P ⊆ A := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha|ha
        · rcases Finset.mem_erase.mp ha with ⟨ne,mem⟩
          exact (Finset.mem_insert.mp (hT mem)).resolve_left ne
        · exact hP ha
      have new : ¬available (T.erase y ∪ P) y := by
        rintro (mem|h|h)
        · exact fresh (.inl (sub mem))
        · exact fresh (.inr (.inl h))
        · exact fresh (.inr (.inr h))
      exact ⟨_,sub,_,Nat.add_le_add_right hb _,_,Nat.add_le_add_right ht _,.step fact hy new sl⟩
    · refine ⟨T, ?_,bb, by omega,tt,by omega,sl⟩
      intro a ha
      rcases Finset.mem_insert.mp (hT ha) with rfl|h
      · exact False.elim (hy ha)
      · exact h

omit [DecidableEq α] in
theorem ExactOp.card {P : Finset (Mask α)} {neg : Bool} {y : Mask α}
    (op : ExactOp P neg y) : P.card = (if neg then 1 else 2) := by
  cases op with
  | neg => simp
  | conj a b h => simp [h]
  | disj a b h => simp [h]

omit [DecidableEq α] in
theorem LiveSlice.card_le {target : Mask α} {b t : ℕ} {S : Finset (Mask α)}
    (sl : LiveSlice target b t S) : S.card ≤ b+1 := by
  induction sl with
  | finish => simp
  | @step b t T P neg y op hy fresh rest ih =>
    have h := Finset.card_union_le (T.erase y) P
    have he := Finset.card_erase_of_mem hy
    have hp := op.card
    have hn := Finset.card_pos.mpr ⟨y,hy⟩
    cases neg <;> simp_all <;> omega
end ProbeFrontier
