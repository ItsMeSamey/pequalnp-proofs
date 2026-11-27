import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
namespace ThreeNameIncidence
open scoped BigOperators
variable {E V : Type*} [DecidableEq E] [DecidableEq V]

/-- Multiplicity of the endpoint v. Loops contribute two. -/
def ends (l r : E → V) (e : E) (v : V) : Nat :=
  (if v = l e then 1 else 0) + (if v = r e then 1 else 0)
def used (l r : E → V) (C : Finset E) := C.image l ∪ C.image r
def degree (l r : E → V) (C : Finset E) (v : V) := ∑ e ∈ C, ends l r e v
/-- Zero incidence sum over the residues modulo two. -/
def BinaryCycle (l r : E → V) (C : Finset E) := ∀ v, degree l r C v % 2 = 0

theorem cycle_of_zero_sum (l r : E → V) (C : Finset E)
    (zero : ∀ v, (∑ e ∈ C, (ends l r e v : ZMod 2)) = 0) : BinaryCycle l r C := by
  intro v
  apply Nat.mod_eq_zero_of_dvd
  apply (ZMod.natCast_eq_zero_iff _ 2).mp
  simpa [degree, Nat.cast_sum] using zero v

theorem handshake (l r : E → V) (C : Finset E) :
    ∑ v ∈ used l r C, degree l r C v = 2 * C.card := by
  unfold degree
  rw [Finset.sum_comm]
  have h (e : E) (he : e ∈ C) : ∑ v ∈ used l r C, ends l r e v = 2 := by
    have hl : l e ∈ used l r C := Finset.mem_union_left _ (Finset.mem_image_of_mem l he)
    have hr : r e ∈ used l r C := Finset.mem_union_right _ (Finset.mem_image_of_mem r he)
    simp [ends, Finset.sum_add_distrib, hl, hr]
  calc
    _ = ∑ _e ∈ C, 2 := Finset.sum_congr rfl h
    _ = _ := by simp [Nat.mul_comm]

private theorem one_end (l r : E → V) (e : E) (v : V)
    (h : l e = v ∨ r e = v) : 1 ≤ ends l r e v := by
  rcases h with h | h <;> subst v <;> simp [ends]

theorem positive_degree (l r : E → V) (C : Finset E) (v : V) (hv : v ∈ used l r C) :
    1 ≤ degree l r C v := by
  obtain ⟨e, he, hv'⟩ : ∃ e ∈ C, l e = v ∨ r e = v := by
    rcases Finset.mem_union.mp hv with hl | hr
    · obtain ⟨e, he, h⟩ := Finset.mem_image.mp hl
      exact ⟨e, he, Or.inl h⟩
    · obtain ⟨e, he, h⟩ := Finset.mem_image.mp hr
      exact ⟨e, he, Or.inr h⟩
  exact (one_end l r e v hv').trans (Finset.single_le_sum (f := fun i => ends l r i v) (fun _ _ => Nat.zero_le _) he)

theorem even_used_degree (l r : E → V) (C : Finset E) (h : BinaryCycle l r C)
    (v : V) (hv : v ∈ used l r C) : 2 ≤ degree l r C v := by
  have hp := positive_degree l r C v hv
  have hz := h v
  omega

theorem strict_excess (l r : E → V) (C : Finset E) (h : BinaryCycle l r C)
    (x : V) (a b d : E) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (included : ({a,b,d} : Finset E) ⊆ C)
    (ha : l a = x ∨ r a = x) (hb : l b = x ∨ r b = x) (hd : l d = x ∨ r d = x) :
    2 * (used l r C).card < ∑ v ∈ used l r C, degree l r C v := by
  have hsmall : (∑ e ∈ ({a,b,d} : Finset E), ends l r e x) ≤ degree l r C x :=
    Finset.sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => Nat.zero_le _)
  simp [hab, had, hbd] at hsmall
  have h1 := one_end l r a x ha
  have h2 := one_end l r b x hb
  have h3 := one_end l r d x hd
  have hpar := h x
  have hcenter : 4 ≤ degree l r C x := by omega
  have ae : a ∈ C := included (by simp)
  have hx : x ∈ used l r C := by
    rcases ha with h | h
    · rw [← h]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem l ae)
    · rw [← h]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem r ae)
  have hsum : (∑ _v ∈ used l r C, (2 : Nat)) < ∑ v ∈ used l r C, degree l r C v :=
    Finset.sum_lt_sum (even_used_degree l r C h) ⟨x, hx, by omega⟩
  simpa [Nat.mul_comm] using hsum

#print axioms handshake
#print axioms strict_excess
end ThreeNameIncidence
