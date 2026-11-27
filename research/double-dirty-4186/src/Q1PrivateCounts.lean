import Q0Transversal

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

open PEqualNP.Outside.L_meta_4186_aux.Q0Transversal

/-- Profiles are symmetric in the two arms. -/
def defect (a b w r s : ℕ) : Prop :=
  (r=2 ∧ s=2 ∧
    ((w=1 ∧ a=3 ∧ b=3) ∨ (w=2 ∧ a+b≤5) ∨ (w=3 ∧ a=2 ∧ b=2))) ∨
  (r=3 ∧ s=3 ∧
    ((w=5 ∧ a=3 ∧ b=3) ∨ (w=6 ∧ a+b≤5) ∨ (w=7 ∧ a=2 ∧ b=2)))

private theorem four_mul_le_pow (k : ℕ) (hk : 4 ≤ k) : 4*k ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

theorem classify {a b w r s : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hw : 1 ≤ w)
    (hr : 2^r ≤ a+w) (hs : 2^s ≤ b+w) :
    2*(r+s) ≤ a+b+w ∨ defect a b w r s := by
  by_cases paid : 2*(r+s) ≤ a+b+w
  · exact Or.inl paid
  right
  have smallR : r ≤ 3 := by
    by_contra! large
    by_cases ord : s ≤ r
    · have := four_mul_le_pow r large; omega
    · have := four_mul_le_pow s (by omega); omega
  have smallS : s ≤ 3 := by
    by_contra! large
    have := four_mul_le_pow s large
    omega
  interval_cases r <;> interval_cases s <;> norm_num [defect] at * <;> omega

/-- Each nonempty matching supplies its own literal-clause certificate.
An empty batch requires no rejecting assignment. -/
theorem bound_with_empty {V : Type*} {k m : ℕ} (pos : 0 < m)
    (pts : Fin k → Bool → V) (cl : Fin m → V → Prop)
    (hits : ∀ c i, cl c (pts i false) ∨ cl c (pts i true))
    (misses : k ≠ 0 → ∀ t : Fin k → Bool, ∃ c, ∀ i, ¬ cl c (pts i (t i))) :
    2^k ≤ m := by
  by_cases h : k=0
  · simp only [h, pow_zero]; omega
  · simpa using pow_le_card pts cl hits (misses h)

/-- On a joint induced matching, a rejected assignment misses a guard clause or
both an A-clause and a B-clause. The union of the latter two hits both batches. -/
theorem union_pow {V : Type*} {a b w r s : ℕ}
    (p : Fin (r+s) → Bool → V) (A : Fin a → V → Prop) (B : Fin b → V → Prop)
    (W : Fin w → V → Prop)
    (guard : ∀ c i, W c (p i false) ∨ W c (p i true))
    (left : ∀ c i, i.val < r → A c (p i false) ∨ A c (p i true))
    (right : ∀ c i, r ≤ i.val → B c (p i false) ∨ B c (p i true))
    (miss : ∀ t : Fin (r+s) → Bool,
      (∃ c, ∀ i, ¬ W c (p i (t i))) ∨
      ((∃ c, ∀ i, ¬ A c (p i (t i))) ∧ (∃ c, ∀ i, ¬ B c (p i (t i))))) :
    2^(r+s) ≤ w+a*b := by
  let member : Fin w ⊕ (Fin a × Fin b) → V → Prop
    | .inl c, v => W c v
    | .inr (c,d), v => A c v ∨ B d v
  have count := pow_le_card p member (by
    intro c i
    cases c with
    | inl c => exact guard c i
    | inr cd =>
      by_cases hi : i.val < r
      · rcases left cd.1 i hi with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · rcases right cd.2 i (by omega) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)) (by
    intro t
    rcases miss t with ⟨c,hc⟩ | ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    · exact ⟨.inl c,hc⟩
    · exact ⟨.inr (c,d), fun i => fun h => h.elim (hc i) (hd i)⟩)
  simpa using count

theorem no_large_defect {a b w : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (bad : defect a b w 3 3) (joint : 2^(3+3) ≤ w+a*b) : False := by
  simp only [defect] at bad
  rcases bad with ⟨h,_⟩ | ⟨_,_,small⟩
  · omega
  rcases small with ⟨rfl,rfl,rfl⟩ | ⟨rfl,h⟩ | ⟨rfl,rfl,rfl⟩
  · norm_num at joint
  · have hA : a ≤ 3 := by omega
    have hB : b ≤ 3 := by omega
    have lim := Nat.mul_le_mul hA hB
    norm_num at joint lim
    omega
  · norm_num at joint

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
