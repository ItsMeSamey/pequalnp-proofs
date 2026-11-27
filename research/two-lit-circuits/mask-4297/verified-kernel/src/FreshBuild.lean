import ProbeFrontier
namespace ProbeFrontier
variable {α : Type} [Fintype α] [DecidableEq α]

inductive FreshOp (S : Finset (Mask α)) : Bool → Mask α → Prop where
  | neg (a : Mask α) (ha : a ∈ S) : FreshOp S true (fun p => !(a p))
  | conj (a b : Mask α) (ha : a ∈ S) (hb : b ∈ S) (diff : a ≠ b) :
      FreshOp S false (fun p => a p && b p)
  | disj (a b : Mask α) (ha : a ∈ S) (hb : b ∈ S) (diff : a ≠ b) :
      FreshOp S false (fun p => a p || b p)

inductive Build (target : Mask α) : ℕ → ℕ → Finset (Mask α) → Prop where
  | finish (S) (h : target ∈ S) : Build target 0 0 S
  | step {b t : ℕ} {A : Finset (Mask α)} {neg : Bool} {y : Mask α}
      (op : FreshOp A neg y) (fresh : ¬available A y)
      (rest : Build target b t (insert y A)) :
      Build target (b + if neg then 0 else 1) (t + if neg then 1 else 0) A

private theorem extend_available {S A : Finset (Mask α)} (ext : ∀ x ∈ S, available A x)
    {x : Mask α} (hx : available S x) : available A x := by
  rcases hx with hx|hx|hx
  · exact ext _ hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr hx)

theorem Operation.toFresh {S A : Finset (Mask α)} {neg : Bool} {y : Mask α}
    (op : Operation S neg y) (ext : ∀ x ∈ S, available A x) (fresh : ¬available A y) :
    FreshOp A neg y := by
  cases op with
  | neg a ha =>
    rcases extend_available ext ha with ha|rfl|rfl
    · exact FreshOp.neg _ ha
    · exact (fresh (Or.inr (Or.inr rfl))).elim
    · exact (fresh (Or.inr (Or.inl rfl))).elim
  | conj a b ha hb =>
    have va := extend_available ext ha
    have vb := extend_available ext hb
    rcases va with aa|rfl|rfl
    · rcases vb with bb|rfl|rfl
      · by_cases eq : a=b
        · subst b
          exact (fresh (Or.inl (by simpa using aa))).elim
        · exact FreshOp.conj _ _ aa bb eq
      · exact (fresh (Or.inr (Or.inl (by funext; simp [zero])))).elim
      · exact (fresh (Or.inl (by simpa [one] using aa))).elim
    · exact (fresh (Or.inr (Or.inl (by funext; simp [zero])))).elim
    · exact (fresh (by simpa [one] using vb)).elim
  | disj a b ha hb =>
    have va := extend_available ext ha
    have vb := extend_available ext hb
    rcases va with aa|rfl|rfl
    · rcases vb with bb|rfl|rfl
      · by_cases eq : a=b
        · subst b
          exact (fresh (Or.inl (by simpa using aa))).elim
        · exact FreshOp.disj _ _ aa bb eq
      · exact (fresh (Or.inl (by simpa [zero] using aa))).elim
      · exact (fresh (Or.inr (Or.inr (by funext; simp [one])))).elim
    · exact (fresh (by simpa [zero] using vb)).elim
    · exact (fresh (Or.inr (Or.inr (by funext; simp [one])))).elim

theorem Run.toBuild {target : Mask α} {b t : ℕ} {S : Finset (Mask α)}
    (run : Run target b t S) (nt : target ≠ zero) (nf : target ≠ one)
    (A : Finset (Mask α)) (ext : ∀ x ∈ S, available A x) :
    ∃ b' t', b' ≤ b ∧ t' ≤ t ∧ Build target b' t' A := by
  induction run generalizing A with
  | finish S h =>
    rcases extend_available ext h with ht|ht|ht
    · exact ⟨0,0,le_rfl,le_rfl,Build.finish _ ht⟩
    · exact (nt ht).elim
    · exact (nf ht).elim
  | @step b t S T neg y op next rest ih =>
    by_cases h : available A y
    · obtain ⟨k,l,hk,hl,built⟩ := ih A (fun x hx => by
        rcases Finset.mem_insert.mp (next hx) with rfl|old
        · exact h
        · exact ext _ old)
      exact ⟨k,l,by omega,by omega,built⟩
    · have clean := op.toFresh ext h
      obtain ⟨k,l,hk,hl,built⟩ := ih (insert y A) (fun x hx => by
        rcases Finset.mem_insert.mp (next hx) with rfl|old
        · exact Or.inl (Finset.mem_insert_self ..)
        · rcases ext _ old with mem|z|o
          · exact Or.inl (Finset.mem_insert_of_mem mem)
          · exact Or.inr (Or.inl z)
          · exact Or.inr (Or.inr o))
      exact ⟨_,_,by omega,by omega,Build.step clean h built⟩

end ProbeFrontier
