import ThresholdSharpScaleBand
namespace ThresholdSharpScaleBand

/-- v is the relative tolerance spent here (choose u/10); vP≥2^20
pays all gate-level constant terms. X≥P suffices at this stage. -/
theorem relative (t E h K P X v : ℝ) (pp : 14≤P) (xp : P≤X)
    (vp : 0≤v) (small : v≤1/3) (cut : (2:ℝ)^20≤v*P)
    (time : t=X^10) (lowE : X^6≤(2:ℝ)^16*E) (highE : E≤P*X^6)
    (lowH : t-4*P*X^8≤h) (highH : h≤t+4*P*X^8)
    (eq : 2*K=2*t*E+E^2+7*t+7*E+14) :
    (1-v)*t≤h ∧ t≤2*h ∧ h≤2*t ∧ K≤(1+3*v)*h*E := by
  have x1 : 1≤X := by linarith
  have xn : 0≤X := by linarith
  have vx := mul_le_mul_of_nonneg_left xp vp
  have vv : 16≤v*X := by norm_num at cut; linarith
  have sq : 16*P≤v*X^2 := by nlinarith only [mul_le_mul_of_nonneg_right vv xn,xp]
  have err := mul_le_mul_of_nonneg_right sq (pow_nonneg xn 8)
  subst t
  have xt : 0≤X^10 := pow_nonneg xn 10
  have vt : 0≤v*X^10 := mul_nonneg vp xt
  have pe : 0≤P*X^8 := mul_nonneg (by linarith) (pow_nonneg xn 8)
  have half : X^10≤2*h := by nlinarith only [lowH,err,xt,vt,pe,mul_le_mul_of_nonneg_right small (pow_nonneg xn 10)]
  have two : h≤2*X^10 := by nlinarith only [highH,err,xt,vt,pe,mul_le_mul_of_nonneg_right small (pow_nonneg xn 10)]
  have ord : (1-v)*X^10≤h := by nlinarith only [lowH,err,xt,vt,pe,mul_nonneg vp (pow_nonneg xn 10)]
  have head : X^10≤h+v*h := by nlinarith only [lowH,err,xt,vt,pe,mul_le_mul_of_nonneg_left half vp]
  have x68 : X^6≤X^8 := pow_le_pow_right₀ x1 (by decide)
  have ep : 0≤E := by nlinarith only [lowE,pow_nonneg xn 6]
  have vh : E≤v*h := by nlinarith only [highE,mul_le_mul_of_nonneg_left x68 (show 0≤P by linarith),
    err,vt,pe,mul_le_mul_of_nonneg_left half vp]
  have x16 : X≤X^6 := by simpa using (pow_le_pow_right₀ x1 (by decide : 1≤6))
  have x110 : X≤X^10 := by simpa using (pow_le_pow_right₀ x1 (by decide : 1≤10))
  have ve : 14≤v*E := by
    have l := mul_le_mul_of_nonneg_left lowE vp
    have k := mul_le_mul_of_nonneg_left x16 vp
    norm_num at cut l
    linarith
  have bigH : 1≤h := by linarith
  have lin : 7≤v*h := by nlinarith only [vv,mul_le_mul_of_nonneg_left x110 vp,mul_le_mul_of_nonneg_left half vp]
  have base : 7*X^10≤v*h*E := by nlinarith only [half,mul_le_mul_of_nonneg_right ve (show 0≤h by linarith)]
  have off : 14≤v*h*E := by nlinarith only [bigH,mul_le_mul_of_nonneg_right ve (show 0≤h by linarith)]
  exact ⟨ord,half,two,budget_relative _ _ _ _ _ ep head vh base lin off eq⟩

#print axioms relative
end ThresholdSharpScaleBand
