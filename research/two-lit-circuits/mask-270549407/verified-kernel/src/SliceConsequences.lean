import SliceUnate
namespace ProbeFrontier
variable {α : Type} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem LiveSlice.asRun {target : Mask α} {b t : ℕ} {S : Finset (Mask α)}
    (sl : LiveSlice target b t S) : Run target b t S := by
  induction sl with
  | finish => exact .finish _ (.inl (by simp))
  | @step b t T P n y op hy fresh rest ih =>
    refine .step (S := T.erase y ∪ P) (T := T) (y := y) ?_ ?_ ih
    · cases op with
      | neg a => exact .neg a (.inl (by simp))
      | conj a b diff => exact .conj a b (.inl (by simp)) (.inl (by simp))
      | disj a b diff => exact .disj a b (.inl (by simp)) (.inl (by simp))
    · intro a ha
      by_cases heq : a=y
      · simp [heq]
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq,ha⟩))

omit [DecidableEq α] in
theorem LiveSlice.monotone {target : Mask α} {b t : ℕ} {S : Finset (Mask α)}
    (sl : LiveSlice target b t S) (noNot : t=0) (i j : α)
    (h : ∀ a ∈ S, a i ≤ a j) : target i ≤ target j := by
  induction sl with
  | finish => exact h _ (by simp)
  | @step b t T P n y op hy fresh rest ih =>
    cases n with
    | true => simp at noNot
    | false =>
      apply ih (by simpa using noNot)
      intro a ha
      by_cases eq : a=y
      · subst a
        have hd := op.directed true i j (by
          intro x hx
          simpa [Directed] using h x (Finset.mem_union_right _ hx))
        simpa [Directed] using hd
      · exact h a (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ha⟩))

omit [DecidableEq α] in
theorem UnateOn.no_opposite {target a : Mask α} {S : Finset (Mask α)}
    (u : UnateOn S target) (p n q m : α)
    (hp : target p = true) (hn : target n = false)
    (hq : target q = true) (hm : target m = false)
    (hap : a p = false) (han : a n = true)
    (haq : a q = true) (ham : a m = false)
    (eq1 : ∀ x ∈ S, x ≠ a → x p = x n) (eq2 : ∀ x ∈ S, x ≠ a → x q = x m) : False := by
  obtain ⟨σ,mono⟩ := u
  cases dir : σ a with
  | true =>
    have bad := mono p n (by
      intro x hx
      by_cases e : x=a
      · subst x; simp [Directed,dir,hap,han]
      · simp [Directed,eq1 x hx e])
    simp [hp,hn] at bad
    exact (by decide : ¬(true ≤ false)) bad
  | false =>
    have bad := mono q m (by
      intro x hx
      by_cases e : x=a
      · subst x; simp [Directed,dir,haq,ham]
      · simp [Directed,eq2 x hx e])
    simp [hq,hm] at bad
    exact (by decide : ¬(true ≤ false)) bad
end ProbeFrontier
