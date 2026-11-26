import Research.CrownCollisionLimit

namespace CrownCharge
open scoped BigOperators

theorem sum_cover {ι κ : Type*} [DecidableEq κ]
    (I : Finset ι) (E : Finset κ) (F : ι → Finset κ) (wt : κ → ℚ)
    (nonneg : ∀ x, 0 ≤ wt x) (cover : ∀ x ∈ E, ∃ k ∈ I, x ∈ F k) :
    ∑ x ∈ E, wt x ≤ ∑ k ∈ I, ∑ x ∈ F k, wt x := by
  classical
  calc
    _ ≤ ∑ x ∈ E, ∑ k ∈ I, if x ∈ F k then wt x else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨k,hk,hit⟩ := cover x hx
      have h := Finset.single_le_sum (f := fun k => if x ∈ F k then wt x else 0)
        (s := I) (fun j _ => by split <;> first | exact nonneg x | rfl) hk
      simpa only [ite_eq_left hit] using h
    _ = ∑ k ∈ I, ∑ x ∈ E, if x ∈ F k then wt x else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · exact fun x _ _ => nonneg x

theorem rectangle_weight {α β : Type*} (R : Finset α) (C : Finset β)
    (r : α → ℚ) (c : β → ℚ) :
    ∑ x ∈ R ×ˢ C, r x.1 * c x.2 = (∑ u ∈ R, r u) * ∑ v ∈ C, c v := by
  rw [Finset.sum_product R C (fun x => r x.1 * c x.2), Finset.sum_mul]
  simp_rw [Finset.mul_sum]

theorem crossed_rectangle_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R₁ R₂ : Finset α) (C₁ C₂ : Finset β) (r : α → ℚ) (c : β → ℚ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j) :
    ∑ x ∈ (R₁ ×ˢ C₂) ∪ (R₂ ×ˢ C₁), r x.1 * c x.2 ≤
      ((∑ u ∈ R₁, r u) + ∑ v ∈ C₁, c v) * ((∑ u ∈ R₂, r u) + ∑ v ∈ C₂, c v) := by
  let f (x : α × β) := r x.1 * c x.2
  have union := Finset.sum_union_inter (s₁ := R₁ ×ˢ C₂) (s₂ := R₂ ×ˢ C₁) (f := f)
  have cap : 0 ≤ ∑ x ∈ (R₁ ×ˢ C₂) ∩ (R₂ ×ˢ C₁), f x :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hr x.1) (hc x.2))
  change ∑ x ∈ (R₁ ×ˢ C₂) ∪ (R₂ ×ˢ C₁), f x ≤ _
  calc
    _ ≤ (∑ x ∈ R₁ ×ˢ C₂, f x) + ∑ x ∈ R₂ ×ˢ C₁, f x := by linarith
    _ = (∑ u ∈ R₁, r u) * (∑ v ∈ C₂, c v) + (∑ u ∈ R₂, r u) * (∑ v ∈ C₁, c v) := by
      rw [show (∑ x ∈ R₁ ×ˢ C₂, f x) = _ from rectangle_weight _ _ _ _,
        show (∑ x ∈ R₂ ×ˢ C₁, f x) = _ from rectangle_weight _ _ _ _]
    _ ≤ _ := by
      have h₁ := mul_nonneg (Finset.sum_nonneg (s := R₁) (fun u _ => hr u))
        (Finset.sum_nonneg (s := R₂) (fun u _ => hr u))
      have h₂ := mul_nonneg (Finset.sum_nonneg (s := C₁) (fun v _ => hc v))
        (Finset.sum_nonneg (s := C₂) (fun v _ => hc v))
      linarith only [h₁,h₂]

end CrownCharge
