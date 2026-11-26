import ThresholdSharpArithmetic
import Mathlib.Data.Nat.Choose.Basic

namespace ThresholdSharpArithmetic

theorem twice_choose_two (h : ℕ) :
    2*((h.choose 2:ℕ):ℤ)=(h:ℤ)*((h:ℤ)-1) := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [Nat.choose_succ_succ h 1,Nat.choose_one_right]
    push_cast
    nlinarith

/-- Convert raw natural class counts. Nonemptiness licenses the cast of h-1.
Funding may be an inequality: unused surplus makes the numerical floor weaker. -/
theorem tally_of_nat_classes {n g h e₀ e₁ e₂ miss dO dA : ℕ}
    (nonempty : 1≤h) (edges : n=e₀+e₁+e₂) (avoid : e₀≤4)
    (boundary : e₁≤3*h+dO+miss+(h-1)*dO+h*dA)
    (missing : miss+e₂≤h.choose 2) (budget : dO+dA+h+2*n≤g+1) :
    Tally (n:ℤ) ((g:ℤ)-2*(n:ℤ)) (h:ℤ) := by
  have edge' : (n:ℤ)=(e₀:ℤ)+(e₁:ℤ)+(e₂:ℤ) := by exact_mod_cast edges
  have avoid' : (e₀:ℤ)≤4 := by exact_mod_cast avoid
  have boundary' :
      (e₁:ℤ) ≤ 3*(h:ℤ)+(dO:ℤ)+(miss:ℤ)+(((h-1:ℕ):ℤ))*(dO:ℤ)+(h:ℤ)*(dA:ℤ) := by
    exact_mod_cast boundary
  rw [Nat.cast_sub nonempty, Nat.cast_one] at boundary'
  have miss' : (miss:ℤ)+(e₂:ℤ)≤((h.choose 2:ℕ):ℤ) := by exact_mod_cast missing
  have fin : (dO:ℤ)+(dA:ℤ)+(h:ℤ)+2*(n:ℤ)≤(g:ℤ)+1 := by exact_mod_cast budget
  have mult := mul_le_mul_of_nonneg_left
    (show (dO:ℤ)+(dA:ℤ)≤(g:ℤ)-2*(n:ℤ)+1-(h:ℤ) by omega)
    (show 0≤(h:ℤ) by exact_mod_cast (Nat.zero_le h))
  unfold Tally
  nlinarith only [edge', avoid', boundary', miss', mult, twice_choose_two h]

theorem tally_empty {n g : ℕ} (hn : n≤4) :
    Tally (n:ℤ) ((g:ℤ)-2*(n:ℤ)) 0 := by
  have h : (n:ℤ)≤4 := by exact_mod_cast hn
  unfold Tally
  nlinarith

end ThresholdSharpArithmetic
