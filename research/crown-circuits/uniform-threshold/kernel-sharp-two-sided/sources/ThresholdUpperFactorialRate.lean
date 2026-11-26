import ThresholdUpperScalarRate
import Mathlib.Data.Nat.Choose.Basic
namespace ThresholdUpperFactorialRate

theorem sample_identity (N v j : ℕ) (h : j≤v) :
    (N-j).choose (v-j)*N.descFactorial j = N.choose v*v.descFactorial j := by
  simp only [Nat.descFactorial_eq_factorial_mul_choose]
  have id := congrArg (fun a : ℕ => j.factorial*a) (Nat.choose_mul (n:=N) h)
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using id.symm

theorem sampled_powers (N v j : ℕ) (fit : j≤v) (room : v≤N) :
    v.descFactorial j*N^j≤N.descFactorial j*v^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have cap : j≤v := by omega
    have prev := ih cap
    have one : (v-j)*N≤(N-j)*v := by
      have a : v-j+j=v := Nat.sub_add_cancel cap
      have b : N-j+j=N := Nat.sub_add_cancel (cap.trans room)
      nlinarith only [congrArg (fun z : ℕ => z*N) a,congrArg (fun z : ℕ => z*v) b,
        Nat.mul_le_mul_left j room]
    have both := Nat.mul_le_mul one prev
    simpa only [Nat.descFactorial_succ,pow_succ,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using both

theorem factorial_power (k : ℕ) : (k/10+1)^(9*k)≤k.factorial^10 := by
  let r := k-k/10
  have rk : r≤k := Nat.sub_le _ _
  have base := Nat.pow_sub_le_descFactorial k r
  have eq : k+1-r=k/10+1 := by dsimp [r]; omega
  rw [eq] at base
  have pay : k.descFactorial r≤k.factorial := by
    rw [←Nat.factorial_mul_descFactorial rk]
    exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  have price := Nat.pow_le_pow_left (base.trans pay) 10
  rw [←pow_mul] at price
  have size : 9*k≤r*10 := by dsimp [r]; omega
  exact (Nat.pow_le_pow_right (by omega) size).trans price

#print axioms sample_identity
#print axioms sampled_powers
#print axioms factorial_power
end ThresholdUpperFactorialRate
