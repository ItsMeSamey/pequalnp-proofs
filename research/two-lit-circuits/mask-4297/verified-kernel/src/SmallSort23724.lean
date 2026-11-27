import Std
namespace Numeric23724

def insNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insNat a bs

def insSort : List Nat → List Nat
  | [] => []
  | a :: s => insNat a (insSort s)

private theorem insNat_perm (a : Nat) (s : List Nat) : (insNat a s).Perm (a :: s) := by
  induction s with
  | nil => exact .refl _
  | cons b s ih =>
    simp only [insNat]
    split
    · exact .refl _
    · exact (ih.cons b).trans (.swap _ _ _)

private theorem insSort_perm (s : List Nat) : (insSort s).Perm s := by
  induction s with
  | nil => exact .refl _
  | cons a s ih => exact (insNat_perm a _).trans (ih.cons a)

private theorem insNat_sorted (a : Nat) (s : List Nat) (h : s.Pairwise (· ≤ ·)) :
    (insNat a s).Pairwise (· ≤ ·) := by
  induction s with
  | nil => simp [insNat]
  | cons b s ih =>
    obtain ⟨hb,hr⟩ := List.pairwise_cons.mp h
    simp only [insNat]
    split
    next hab =>
      apply List.pairwise_cons.mpr
      refine ⟨?_,h⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · exact hab
      · exact Nat.le_trans hab (hb x hx)
    next hab =>
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih hr⟩
      intro x hx
      rcases List.mem_cons.mp ((insNat_perm a s).mem_iff.mp hx) with rfl|hx
      · omega
      · exact hb x hx

private theorem insSort_sorted (s : List Nat) : (insSort s).Pairwise (· ≤ ·) := by
  induction s with
  | nil => exact .nil
  | cons a s ih => exact insNat_sorted a _ ih

theorem mergeSort_eq_insSort (s : List Nat) : s.mergeSort = insSort s := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _; exact Nat.le_antisymm
  · have h := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
        (by simp; omega) (by simp; omega) s
    simpa using h
  · exact insSort_sorted s
  · exact (List.mergeSort_perm s _).trans (insSort_perm s).symm
end Numeric23724
