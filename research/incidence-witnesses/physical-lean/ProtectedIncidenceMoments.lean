import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace ProtectedIncidenceMoments
open Finset

theorem packing_exact {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : α → Finset β) (S : Finset α) (D : Finset β) (q : ℕ)
    (lower : ∀ a ∈ S, q ≤ (D ∩ F a).card)
    (upper : ∀ a ∈ S, (D ∩ F a).card ≤ q)
    (overlap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (D ∩ (F a ∩ F b)).card ≤ 1) :
    q^2 * S.card^2 ≤ D.card * S.card * (q+S.card-1) := by
  let f (a : α) (x : β) : ℕ := if x ∈ F a then 1 else 0
  let occ (x : β) := ∑ a ∈ S, f a x
  have single (a : α) : ∑ x ∈ D, f a x = (D ∩ F a).card := by
    simp [f, ← Finset.filter_mem_eq_inter]
  have pair (a b : α) : ∑ x ∈ D, f a x * f b x = (D ∩ (F a ∩ F b)).card := by
    have term (x : β) : f a x * f b x = if x ∈ F a ∩ F b then 1 else 0 := by
      by_cases ha : x ∈ F a <;> by_cases hb : x ∈ F b <;> simp [f,ha,hb]
    simp [term, ← Finset.filter_mem_eq_inter]
  have mass : S.card*q ≤ ∑ x ∈ D, occ x := by
    dsimp [occ]
    rw [Finset.sum_comm]
    simpa [single] using Finset.sum_le_sum lower
  have row (a : α) (ha : a ∈ S) :
      ∑ b ∈ S, (D ∩ (F a ∩ F b)).card ≤ q+S.card-1 := by
    rw [← Finset.sum_erase_add _ _ ha]
    have off : ∑ b ∈ S.erase a, (D ∩ (F a ∩ F b)).card ≤ (S.erase a).card := by
      simpa using Finset.sum_le_sum (s := S.erase a) (g := fun _ => 1)
        (fun b hb => overlap a ha b (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp hb).1.symm)
    simp only [Finset.inter_self]
    have := upper a ha
    rw [Finset.card_erase_of_mem ha] at off
    have := Finset.card_pos.mpr ⟨a,ha⟩
    omega
  have moment : ∑ x ∈ D, occ x ^ 2 ≤ S.card*(q+S.card-1) := by
    calc
      _ = ∑ a ∈ S, ∑ b ∈ S, ∑ x ∈ D, f a x * f b x := by
        simp only [occ, pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        simp only [Nat.mul_comm]
      _ ≤ _ := by simpa [pair] using Finset.sum_le_sum row
  calc
    _ = (S.card*q)^2 := by ring
    _ ≤ (∑ x ∈ D, occ x)^2 := Nat.pow_le_pow_left mass 2
    _ ≤ D.card * ∑ x ∈ D, occ x^2 := by simpa using Finset.sum_mul_sq_le_sq_mul_sq D (fun _ => 1) occ
    _ ≤ _ := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left D.card moment


/-- Trim each marked site's lost neighbors to exactly 376 before applying
    the second-moment bound. Different sites may share deleted neighbors. -/
theorem marks_401 {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : α → Finset β) (S : Finset α) (D : Finset β)
    (lost : ∀ a ∈ S, 376 ≤ (D ∩ F a).card)
    (overlap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (D ∩ (F a ∩ F b)).card ≤ 1)
    (budget : D.card ≤ 38808) : S.card ≤ 141 := by
  classical
  let G (a : α) : Finset β :=
    if ha : a ∈ S then (Finset.exists_subset_card_eq (lost a ha)).choose else ∅
  have spec (a) (ha : a ∈ S) : G a ⊆ D ∩ F a ∧ (G a).card = 376 := by
    simpa [G,ha] using (Finset.exists_subset_card_eq (lost a ha)).choose_spec
  have exactCard (a) (ha : a ∈ S) : (D ∩ G a).card = 376 := by
    have hsub : G a ⊆ D := fun x hx => (Finset.mem_inter.mp ((spec a ha).1 hx)).1
    rw [Finset.inter_eq_right.mpr hsub]
    exact (spec a ha).2
  have distinct (a) (ha : a ∈ S) (b) (hb : b ∈ S) (ab : a ≠ b) :
      (D ∩ (G a ∩ G b)).card ≤ 1 := by
    apply le_trans (Finset.card_le_card (t := D ∩ (F a ∩ F b)) ?_) (overlap a ha b hb ab)
    intro x hx
    obtain ⟨xd,xab⟩ := Finset.mem_inter.mp hx
    obtain ⟨xa,xb⟩ := Finset.mem_inter.mp xab
    exact Finset.mem_inter.mpr ⟨xd, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp ((spec a ha).1 xa)).2, (Finset.mem_inter.mp ((spec b hb).1 xb)).2⟩⟩
  have pack := packing_exact G S D 376
    (fun a ha => (exactCard a ha).ge) (fun a ha => (exactCard a ha).le) distinct
  by_cases empty : S.card = 0
  · omega
  have hmul : S.card * (376^2 * S.card) ≤ S.card * (D.card * (376+S.card-1)) := by
    simpa [pow_two,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using pack
  have h := Nat.le_of_mul_le_mul_left hmul (Nat.pos_of_ne_zero empty)
  have normalized : 376 + S.card - 1 = 375 + S.card := by omega
  rw [normalized] at h
  have upper := h.trans (Nat.mul_le_mul_right (375+S.card) budget)
  omega

end ProtectedIncidenceMoments
