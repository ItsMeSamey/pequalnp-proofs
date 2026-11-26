import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
namespace ThresholdUpperRound

set_option maxRecDepth 4096 in
/-- x=t^(1/100), y=v^(1/100). Multiplying all fractional exponents by 100
allows comparison of integer powers without differentiating ceiling terms. -/
theorem slack {x y a C v n : ℝ} (x1 : 1≤x) (big : (2:ℝ)^170*(C+1)≤x)
    (c0 : 0≤C) (a0 : 0≤a) (a1 : a≤1) (y0 : 0≤y)
    (vdef : y^100=v) (ndef : 2*n=x^200)
    (vlo : x^100+a*x^60+x^58≤v)
    (vhi : v≤x^100+a*x^60+x^58+1) :
    n≤(v^2-v)/2-a*y^160-C*y^155 := by
  have x0 : 0≤x := by linarith
  have inc {i j : Nat} (h : i≤j) : x^i≤x^j := pow_le_pow_right₀ x1 h
  have ax := mul_le_mul_of_nonneg_right a1 (pow_nonneg x0 60)
  have x58 := inc (by decide : 58≤60)
  have x60 := inc (by decide : 60≤80)
  have x80 := inc (by decide : 80≤100)
  have base : 1≤x^60 := by simpa using inc (by decide : 0≤60)
  have widen : y^20≤x^20+1 := by
    by_contra! bad
    have p := pow_lt_pow_left₀ bad (by positivity : 0≤x^20+1) (by decide : 5≠0)
    nlinarith only [p,vdef,vhi,ax,x58,x60,base,pow_nonneg x0 20,pow_nonneg x0 40,pow_nonneg x0 60]
  have rough : y≤2*x := by
    by_contra! bad
    have p : (2*x)^20<y^20 := pow_lt_pow_left₀ bad (by linarith) (by decide)
    rw [mul_pow] at p
    have unit : 1≤x^20 := by simpa using inc (by decide : 0≤20)
    norm_num at p
    linarith only [p,widen,unit]
  have y8 := pow_le_pow_left₀ (pow_nonneg y0 20) widen 8
  have expand : y^160≤x^160+255*x^140 := by
    nlinarith only [y8,inc (by decide : 0≤140),inc (by decide : 20≤140),
      inc (by decide : 40≤140),inc (by decide : 60≤140),inc (by decide : 80≤140),
      inc (by decide : 100≤140),inc (by decide : 120≤140)]
  have ey := mul_le_mul_of_nonneg_left expand a0
  have e2 := mul_le_mul_of_nonneg_right a1 (pow_nonneg x0 140)
  have rem := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ y0 rough 155) c0
  have scale := mul_le_mul_of_nonneg_right big (pow_nonneg x0 155)
  have save := mul_le_mul_of_nonneg_left vlo (pow_nonneg x0 100)
  have sq := sq_nonneg (v-x^100)
  nlinarith only [ndef,vhi,ax,x58,base,save,sq,ey,e2,scale,rem,
    inc (by decide : 156≤158),inc (by decide : 140≤155),inc (by decide : 100≤155),
    inc (by decide : 60≤155),inc (by decide : 0≤155),
    mul_nonneg c0 (pow_nonneg x0 155),pow_nonneg x0 155]
end ThresholdUpperRound
