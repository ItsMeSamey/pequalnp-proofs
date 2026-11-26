import LiveSlice
namespace ProbeFrontier
variable {α : Type} [Fintype α] [DecidableEq α]

def Directed (d : Bool) (a : Mask α) (i j : α) : Prop :=
  if d then a i ≤ a j else a j ≤ a i

def UnateOn (S : Finset (Mask α)) (target : Mask α) : Prop :=
  ∃ σ : Mask α → Bool, ∀ i j, (∀ a ∈ S, Directed (σ a) a i j) → target i ≤ target j

omit [DecidableEq α] in
theorem ExactOp.directed {P : Finset (Mask α)} {n : Bool} {y : Mask α}
    (op : ExactOp P n y) (d : Bool) (i j : α)
    (hs : ∀ a ∈ P, Directed (if n then !d else d) a i j) : Directed d y i j := by
  cases op with
  | neg a =>
    have ha := hs a (by simp)
    cases d <;> cases hi : a i <;> cases hj : a j <;> simp_all [Directed]
  | conj a b h =>
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    cases d <;> cases ai : a i <;> cases aj : a j <;> cases bi : b i <;> cases bj : b j <;> simp_all [Directed]
  | disj a b h =>
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    cases d <;> cases ai : a i <;> cases aj : a j <;> cases bi : b i <;> cases bj : b j <;> simp_all [Directed]

omit [DecidableEq α] in
theorem LiveSlice.unate {target : Mask α} {b t : ℕ} {S : Finset (Mask α)}
    (sl : LiveSlice target b t S) (tight : S.card = b+1) : UnateOn S target := by
  induction sl with
  | finish =>
    refine ⟨fun _ => true, ?_⟩
    intro i j h
    simpa [Directed] using h target (by simp)
  | @step b t T P n y op hy fresh rest ih =>
    have hr := rest.card_le
    have hsum := Finset.card_union_add_card_inter (T.erase y) P
    have he := Finset.card_erase_of_mem hy
    have hn := Finset.card_pos.mpr ⟨y,hy⟩
    have hp := op.card
    have dims : T.card = b+1 ∧ ((T.erase y) ∩ P).card = 0 := by
      cases n <;> simp only [Bool.false_eq_true, ite_false, ite_true] at * <;> omega
    obtain ⟨σ,hσ⟩ := ih dims.1
    let d := if n then !(σ y) else σ y
    let τ := fun a : Mask α => if a ∈ P then d else σ a
    refine ⟨τ, ?_⟩
    intro i j h
    apply hσ
    intro a ha
    by_cases eq : a=y
    · subst a
      apply op.directed
      intro x hx
      simpa [τ,d,hx] using h x (Finset.mem_union_right _ hx)
    · have hold : a ∈ T.erase y := Finset.mem_erase.mpr ⟨eq,ha⟩
      have hno : a ∉ P := by
        intro hh
        have hin := Finset.mem_inter.mpr ⟨hold,hh⟩
        have hempty := Finset.card_eq_zero.mp dims.2
        rw [hempty] at hin
        simp at hin
      simpa [τ,hno] using h a (Finset.mem_union_left _ hold)
end ProbeFrontier
