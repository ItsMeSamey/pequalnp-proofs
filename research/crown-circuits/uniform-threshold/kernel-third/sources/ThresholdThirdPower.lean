import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ThresholdThirdPower

/-- Final receiver-ledger multiplication. Q counts ordered four-cycles. -/
theorem ledger_power (t h E M w g Q : ℝ) (ht : 0≤t) (hh : 0<h) (he : 0≤E)
    (hm : 0≤M) (hw : 0≤w) (hq : 0≤Q)
    (htop : t≤2*h) (hg : h≤2*g) (hmiss : M≤180*h*E)
    (hrecv : w≤3000*E) (hcycle : Q≤24*M) (hsuper : 2*g^4≤Q*w^4) :
    t^3≤(2:ℝ)^65*E^5 := by
  have gg : 0≤g := by linarith
  have hfour := pow_le_pow_left₀ hh.le hg 4
  have wfour := pow_le_pow_left₀ hw hrecv 4
  have hc := mul_le_mul_of_nonneg_right hcycle (pow_nonneg hw 4)
  have wc := mul_le_mul_of_nonneg_left wfour (show 0≤24*M by positivity)
  have mc := mul_le_mul_of_nonneg_right hmiss (pow_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3000) he) 4)
  have prod : h*h^3 ≤ h*(16*12*180*3000^4*E^5) := by
    nlinarith only [hfour,hsuper,hc,wc,mc]
  have hthree := (mul_le_mul_iff_right₀ hh).mp prod
  have tthree := pow_le_pow_left₀ ht htop 3
  have e5 : 0≤E^5 := pow_nonneg he _
  nlinarith only [tthree,hthree,e5]

/-- Fifth-power estimate implies an integer-exponent third-order lower
bound. The cutoff pays exactly for the additive one in E. -/
theorem regular_tenth (t n z E : ℝ) (hn : 0≤n) (ht : (2:ℝ)^200≤t)
    (sq : t^2=2*n) (exc : E=1+max 0 z)
    (bound : t^3≤(2:ℝ)^65*E^5) :
    0≤z ∧ n^3≤((2:ℝ)^14*z)^10 := by
  have epos : 0≤E := by rw [exc]; positivity
  have tpos : 0≤t := by linarith
  have cutoff := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2^200) ht 3
  have two : 2≤E := by
    by_contra! small
    have es := pow_le_pow_left₀ epos small.le 5
    norm_num at cutoff es bound ⊢
    linarith
  have zpos : 0≤z := by
    by_contra! neg
    rw [exc,max_eq_left neg.le] at two
    norm_num at two
  have ez : E≤2*z := by rw [max_eq_right zpos] at exc; linarith
  have ef := pow_le_pow_left₀ epos ez 5
  have fifth : t^3≤((2:ℝ)^14*z)^5 := by nlinarith only [bound,ef]
  have squared := pow_le_pow_left₀ (pow_nonneg tpos 3) fifth 2
  have id : (t^3)^2=(2*n)^3 := by calc
    (t^3)^2 = (t^2)^3 := by ring
    _ = _ := by rw [sq]
  rw [id] at squared
  refine ⟨zpos,?_⟩
  nlinarith only [squared,pow_nonneg hn 3]

/-- Transfer to a surviving regular order m≥n/2. z and y are the
unrestricted and regular surpluses above their own square-root terms. -/
theorem transfer_tenth (n m z y : ℝ) (hn : 0≤n) (hm : n≤2*m)
    (hy : 0≤y) (order : y≤z) (reg : m^3≤((2:ℝ)^14*y)^10) :
    n^3≤((2:ℝ)^15*z)^10 := by
  have cube := pow_le_pow_left₀ hn hm 3
  have ten := pow_le_pow_left₀ hy order 10
  have yy := pow_nonneg hy 10
  nlinarith only [cube,reg,ten,yy]

#print axioms ledger_power
#print axioms regular_tenth
#print axioms transfer_tenth
end ThresholdThirdPower
