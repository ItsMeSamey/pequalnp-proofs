import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace GuardRelease
open Matrix

theorem diagonal_completion {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    ∃ d : Fin n → ZMod 2, (A + diagonal d).det ≠ 0 := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨d,hd⟩ := ih (A.submatrix Fin.succ Fin.succ)
    let M (x : ZMod 2) := A + diagonal (Fin.cons x d)
    have minor (x : ZMod 2) (j : Fin (n+1)) :
        (M x).submatrix Fin.succ j.succAbove = (M 0).submatrix Fin.succ j.succAbove := by
      ext i k
      simp [M, submatrix_apply, diagonal_apply]
    have tail : (M 0).submatrix Fin.succ Fin.succ = A.submatrix Fin.succ Fin.succ + diagonal d := by
      ext i j
      simp [M, submatrix_apply, diagonal_apply]
    have zeroAbove : (0 : Fin (n+1)).succAbove = Fin.succ := by funext i; simp
    have diff : (M 1).det = (M 0).det + (A.submatrix Fin.succ Fin.succ + diagonal d).det := by
      rw [det_succ_row_zero (M 1), det_succ_row_zero (M 0)]
      simp only [Fin.sum_univ_succ, minor 1, Fin.val_zero, pow_zero, one_mul,
        zeroAbove, tail]
      have row (x : ZMod 2) (i : Fin n) : M x 0 i.succ = A 0 i.succ := by
        simp [M, Ne.symm (Fin.succ_ne_zero i)]
      simp only [row]
      have head (x : ZMod 2) : M x 0 0 = A 0 0 + x := by simp [M]
      simp only [head]
      ring
    by_cases h : (M 0).det = 0
    · exact ⟨Fin.cons 1 d, by change (M 1).det ≠ 0; rwa [diff,h,zero_add]⟩
    · exact ⟨Fin.cons 0 d,h⟩

theorem diagonal_linear_solver {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    ∃ (d : Fin n → ZMod 2) (S : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)),
      ∀ b, (A + diagonal d).mulVec (S b) = b := by
  obtain ⟨d,hd⟩ := diagonal_completion A
  let M := A + diagonal d
  have hM : IsUnit M := M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd)
  let e := M.toLinearEquiv' (Classical.choice hM.nonempty_invertible)
  exact ⟨d,e.symm, e.apply_symm_apply⟩

end GuardRelease
