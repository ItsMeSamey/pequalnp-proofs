import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace IncidenceMoments
open Finset

theorem packing {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : α → Finset β) (S : Finset α) (D : Finset β) (q : ℕ)
    (lower : ∀ a ∈ S, q ≤ (D ∩ F a).card)
    (upper : ∀ a ∈ S, (D ∩ F a).card ≤ q+1)
    (overlap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (D ∩ (F a ∩ F b)).card ≤ 1) :
    q^2 * S.card^2 ≤ D.card * S.card * (q+S.card) := by
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
      ∑ b ∈ S, (D ∩ (F a ∩ F b)).card ≤ q+S.card := by
    rw [← Finset.sum_erase_add _ _ ha]
    have off : ∑ b ∈ S.erase a, (D ∩ (F a ∩ F b)).card ≤ (S.erase a).card := by
      simpa using Finset.sum_le_sum (s := S.erase a) (g := fun _ => 1)
        (fun b hb => overlap a ha b (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp hb).1.symm)
    simp only [Finset.inter_self]
    have := upper a ha
    rw [Finset.card_erase_of_mem ha] at off
    have := Finset.card_pos.mpr ⟨a,ha⟩
    omega
  have moment : ∑ x ∈ D, occ x ^ 2 ≤ S.card*(q+S.card) := by
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

end IncidenceMoments
