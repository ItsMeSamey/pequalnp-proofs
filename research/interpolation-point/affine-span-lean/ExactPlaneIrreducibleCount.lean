import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

namespace ExactPlaneIrreducibleCount
theorem candidates (n : ℕ) : Fintype.card (Fin n → ZMod 2) = 2^n := by simp

/-- Count candidate monic divisors of degrees one through t. -/
def trials (t : ℕ) := ∑ j ∈ Finset.range t, Fintype.card (Fin (j+1) → ZMod 2)

theorem trials_exact (t : ℕ) : trials t + 2 = 2^(t+1) := by
  induction t with
  | zero => simp [trials]
  | succ t ih =>
    change (∑ j ∈ Finset.range (t+1), Fintype.card (Fin (j+1) → ZMod 2)) + 2 = _
    rw [Finset.sum_range_succ, candidates]
    change trials t + 2^(t+1) + 2 = 2^(t+1+1)
    rw [pow_succ (2:ℕ) (t+1)]
    omega

theorem trial_bound (n : ℕ) : trials (n/2) < 2*Nat.sqrt (2^n) := by
  have h : 2^(n/2) ≤ Nat.sqrt (2^n) := by
    apply Nat.le_sqrt'.2
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have eq := trials_exact (n/2)
  rw [pow_succ] at eq
  omega
#print axioms trial_bound
end ExactPlaneIrreducibleCount
