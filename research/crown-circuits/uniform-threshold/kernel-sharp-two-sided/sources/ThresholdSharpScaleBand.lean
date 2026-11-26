import ThresholdThirdPower
namespace ThresholdSharpScaleBand

/-- X^10=t and t²=2m. B always bounds the signed normalized tenth power. -/
theorem band (m t X E B P : ℝ) (sq : t^2=2*m) (scale : X^10=t) (xp : 0≤X)
    (ep : 0≤E) (pp : 1≤P) (bp : B≤P) (weak : m^3≤((2:ℝ)^15*E)^10)
    (upper : E^10≤B*m^3) : X^6≤(2:ℝ)^16*E ∧ E≤P*X^6 := by
  have id : X^60=8*m^3 := by calc
    X^60=((X^10)^2)^3 := by ring
    _=_ := by rw [scale,sq]; ring
  have xp6 := pow_nonneg xp 6
  constructor
  · by_contra! bad
    have p := pow_lt_pow_left₀ bad (mul_nonneg (by norm_num) ep) (by decide : (10:ℕ)≠0)
    nlinarith only [id,weak,p,pow_nonneg ep 10]
  · have ppos : 0≤P := by linarith
    have big : P≤P^10 := by simpa using (pow_le_pow_right₀ pp (by decide : 1≤10))
    have mp : 0≤m := by nlinarith [sq_nonneg t]
    have mul := mul_le_mul_of_nonneg_right bp (pow_nonneg mp 3)
    have mul' := mul_le_mul_of_nonneg_right big (pow_nonneg mp 3)
    have id' := congrArg (fun z : ℝ => P^10*z) id
    by_contra! bad
    have p := pow_lt_pow_left₀ bad (mul_nonneg ppos xp6) (by decide : (10:ℕ)≠0)
    nlinarith only [upper,mul,mul',id',p,mul_nonneg (pow_nonneg ppos 10) (pow_nonneg mp 3)]

/-- An upper bound on the discriminant with simple finite linear tests. -/
theorem budget (t E K : ℝ) (ep : 0≤E) (tp : 0≤t) (one : 14≤E)
    (small : E≤t/4) (large : 14≤t)
    (eq : 2*K=2*t*E+E^2+7*t+7*E+14) : 2*K≤4*t*E := by
  nlinarith [mul_nonneg ep (show 0≤t/4-E by linarith),
    mul_nonneg tp (show 0≤E-14 by linarith),
    mul_nonneg ep (show 0≤t-14 by linarith),
    mul_nonneg (show 0≤t-1 by linarith) (show 0≤E-1 by linarith)]

/-- The same v controls all one-sided natural-number losses in K/(hE). -/
theorem budget_relative (t E h v K : ℝ) (ep : 0≤E)
    (head : t≤h+v*h) (small : E≤v*h)
    (base : 7*t≤v*h*E) (linear : 7≤v*h) (offset : 14≤v*h*E)
    (eq : 2*K=2*t*E+E^2+7*t+7*E+14) : K≤(1+3*v)*h*E := by
  nlinarith only [eq,base,offset,mul_le_mul_of_nonneg_right head ep,
    mul_le_mul_of_nonneg_right small ep,mul_le_mul_of_nonneg_right linear ep]

/-- Direct bound on h−t that pays the signed d and +1. -/
theorem hub_band (h t E d K P X : ℝ) (xp : 1≤X) (pp : 1≤P) (ep : 0≤E)
    (delta : d=t+E+1-h) (dp : 0≤d) (charge : d^2≤2*K)
    (budget : 2*K≤4*t*E) (time : t=X^10) (band : E≤P*X^6) :
    t-4*P*X^8≤h ∧ h≤t+4*P*X^8 := by
  have xn : 0≤X := by linarith
  have pn : 0≤P := by linarith
  have xx : X^6≤X^8 := pow_le_pow_right₀ xp (by decide)
  have xwide : 1≤X^8 := one_le_pow₀ xp
  have pwide := mul_le_mul_of_nonneg_left xwide pn
  have px := mul_le_mul_of_nonneg_left xx pn
  have cap := mul_le_mul_of_nonneg_left band (pow_nonneg xn 10)
  have p2 : P≤P^2 := by nlinarith [mul_nonneg pn (show 0≤P-1 by linarith)]
  have sqcap := mul_le_mul_of_nonneg_right p2 (pow_nonneg xn 16)
  rw [time] at budget
  have dlim : d≤2*P*X^8 := by
    by_contra! bad
    have p := pow_lt_pow_left₀ bad (show 0≤2*P*X^8 by positivity) (by decide : (2:ℕ)≠0)
    nlinarith only [p,charge,budget,cap,sqcap]
  constructor <;> linarith

#print axioms band
#print axioms budget
#print axioms budget_relative
#print axioms hub_band
end ThresholdSharpScaleBand
