import ThresholdUpperFactorialRate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
namespace ThresholdUpperFirstMoments
open ThresholdUpperFactorialRate

theorem sampled (N v j : ℕ) (fit : j≤v) (room : v≤N) (npos : 0<N) :
    (((N-j).choose (v-j):Nat):ℝ)/(N.choose v:ℝ) ≤ ((v:ℝ)/N)^j := by
  have d : 0<(N.choose v:ℝ) := by exact_mod_cast Nat.choose_pos room
  have p : 0<(N:ℝ) := by exact_mod_cast npos
  have df : 0<(N.descFactorial j:ℝ) := by exact_mod_cast Nat.descFactorial_pos.mpr (fit.trans room)
  have a := sample_identity N v j fit
  have b := sampled_powers N v j fit room
  have eq : (((N-j).choose (v-j):Nat):ℝ)*(N.descFactorial j:ℝ)=(N.choose v:ℝ)*(v.descFactorial j:ℝ) := by exact_mod_cast a
  have le : (v.descFactorial j:ℝ)*(N:ℝ)^j≤(N.descFactorial j:ℝ)*(v:ℝ)^j := by exact_mod_cast b
  rw [div_pow,div_le_div_iff₀ d (pow_pos p _)]
  apply (mul_le_mul_iff_right₀ df).mp
  calc
    _ = ((N.choose v:ℝ)*(v.descFactorial j:ℝ))*(N:ℝ)^j := by rw [←eq]; ring
    _ ≤ (N.choose v:ℝ)*((N.descFactorial j:ℝ)*(v:ℝ)^j) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left le d.le
    _ = _ := by ring

theorem factorial (y : ℝ) (k : ℕ) (big : 10000≤y) (kb : y^50≤(k:ℝ)) :
    (2*y^41)^k≤(k.factorial:ℝ) := by
  have y1 : 1≤y := by linarith
  have yp : 0≤y := by linarith
  let m : ℝ := (k/10+1:Nat)
  have tiny : (k:ℝ)≤10*m := by
    dsimp [m]; exact_mod_cast (by omega : k≤10*(k/10+1))
  have mn : 0≤m := by dsimp [m]; positivity
  have start := pow_le_pow_left₀ (pow_nonneg yp 50) (kb.trans tiny) 9
  have num := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10000) big 4
  have ratio : (2:ℝ)^10*10^9≤y^40 := by
    have monot := pow_le_pow_right₀ y1 (show 4≤40 by decide)
    norm_num at num ⊢; linarith
  have high := mul_le_mul_of_nonneg_right ratio (pow_nonneg yp 410)
  have base : (2*y^41)^10≤m^9 := by nlinarith only [start,high]
  have lifted := pow_le_pow_left₀ (by positivity : 0≤(2*y^41)^10) base k
  have fac : m^(9*k)≤(k.factorial:ℝ)^10 := by dsimp only [m]; exact_mod_cast factorial_power k
  have chain : ((2*y^41)^k)^10≤(k.factorial:ℝ)^10 := by
    calc
      _ = ((2*y^41)^10)^k := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ ≤ (m^9)^k := lifted
      _ ≤ _ := by simpa [←pow_mul] using fac
  by_contra! h
  exact (not_lt_of_ge chain) (pow_lt_pow_left₀ h (by positivity : 0≤(k.factorial:ℝ)) (by decide))

theorem choose_factorial (a k : Nat) :
    (a.choose k:ℝ)*(k.factorial:ℝ)≤(a:ℝ)^k := by
  have base := Nat.descFactorial_le_pow a k
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.mul_comm] at base
  exact_mod_cast base

/-- The actual k-star union-bound numerator, normalized by all v-subsets. -/
theorem star_tail (y : ℝ) (N v w k : ℕ) (big : 10000≤y) (kb : y^50≤(k:ℝ))
    (cw : (w:ℝ)≤3*y^60) (cut : 161≤k) (fit : k≤v) (room : v≤N) (npos : 0<N)
    (ratio : ((w-1:ℕ):ℝ)*((v:ℝ)/N)≤2*y^40) :
    ((w:ℝ)*((w-1).choose k:ℝ)*(((N-k).choose (v-k):Nat):ℝ)/(N.choose v:ℝ))*y^100≤1 := by
  have y1 : 1≤y := by linarith
  have yp : 0<y := by linarith
  have sp := sampled N v k fit room npos
  have comb := choose_factorial (w-1) k
  have fac := factorial y k big kb
  have powratio := pow_le_pow_left₀ (by positivity : 0≤((w-1:ℕ):ℝ)*((v:ℝ)/N)) ratio k
  have cost : ((w-1).choose k:ℝ)*((v:ℝ)/N)^k*y^k≤1 := by
    apply (mul_le_mul_iff_right₀ (show 0<(k.factorial:ℝ) by positivity)).mp
    calc
      _ = (((w-1).choose k:ℝ)*(k.factorial:ℝ))*((v:ℝ)/N)^k*y^k := by ring
      _ ≤ (((w-1:Nat):ℝ)*((v:ℝ)/N))^k*y^k := by
        rw [mul_pow]; gcongr
      _ ≤ (2*y^40)^k*y^k := mul_le_mul_of_nonneg_right powratio (pow_nonneg yp.le _)
      _ = (2*y^41)^k := by rw [←mul_pow]; congr 1; ring
      _ ≤ _ := by simpa using fac
  have pay : (w:ℝ)*y^100≤y^k := by
    have a := mul_le_mul_of_nonneg_right cw (pow_nonneg yp.le 100)
    have b := mul_le_mul_of_nonneg_right (show 3≤y by linarith) (pow_nonneg yp.le 160)
    have c := pow_le_pow_right₀ y1 cut
    nlinarith only [a,b,c]
  calc
    _ = (((N-k).choose (v-k):ℝ)/(N.choose v:ℝ))*(((w-1).choose k:ℝ)*((w:ℝ)*y^100)) := by ring
    _ ≤ ((v:ℝ)/N)^k*(((w-1).choose k:ℝ)*((w:ℝ)*y^100)) := by gcongr
    _ ≤ ((v:ℝ)/N)^k*(((w-1).choose k:ℝ)*y^k) := by gcongr
    _ ≤ 1 := by simpa only [mul_assoc,mul_comm,mul_left_comm] using cost
end ThresholdUpperFirstMoments
