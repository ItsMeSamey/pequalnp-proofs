import ThresholdSharpScaleBand
namespace ThresholdUpperScalarRate

/-- Degree-space comparison after applying the second-stage catalogue rates. -/
theorem injection_error {x A B C : ℝ} (x1 : 1≤x)
    (a : A≤12*x^155) (b : B≤1000000*x^120) (c : C≤2000000*x^130) :
    A+B+C≤4000000*x^155 := by
  have b' : x^120≤x^155 := pow_le_pow_right₀ x1 (by decide)
  have c' : x^130≤x^155 := pow_le_pow_right₀ x1 (by decide)
  have p := pow_nonneg (show 0≤x by linarith) 155
  linarith

/-- Conditioning only costs a lower-order error on top of the sharp cycle constant. -/
theorem condition {q y E L W : ℝ} (yp : 1≤y) (qn : 0≤q) (en : 0≤E)
    (qn' : q*y^100≤1) (half : q≤1/2) (cap : E≤2*y^160)
    (wedge : W≤2*y^140) (conditional : (1-q)*L≤E+W) :
    L≤E+10*y^140 := by
  have yn : 0≤y := by linarith
  have smaller : y^60≤y^140 := pow_le_pow_right₀ yp (by decide)
  have qcost := mul_le_mul_of_nonneg_right qn' (pow_nonneg yn 60)
  have qcap := mul_le_mul_of_nonneg_left cap qn
  have qhalf := mul_le_mul_of_nonneg_right half (pow_nonneg yn 140)
  apply (mul_le_mul_iff_right₀ (show 0<1-q by linarith)).mp
  nlinarith only [conditional,cap,wedge,smaller,qcost,qcap,qhalf,pow_nonneg yn 140]

/-- x^200=2n, x^100 is the leading square root. The surplus may be signed;
a positive tenth-power upper statement uses the independently known lower bound. -/
theorem endpoint {x n beta E δ : ℝ} (x1 : 1≤x) (b0 : 0≤beta) (b2 : beta≤2)
    (nx : x^200=2*n) (ep : 0≤E) (dp : 0≤δ) (cut : (2:ℝ)^51≤δ*x)
    (size : E≤(5*beta/4)*x^60+x^58+7*beta*x^40+2^49*x^45+18) :
    E^10≤8*(5*beta/4+δ)^10*n^3 := by
  have xn : 0≤x := by linarith
  have i40 : x^40≤x^59 := pow_le_pow_right₀ x1 (by decide)
  have i45 : x^45≤x^59 := pow_le_pow_right₀ x1 (by decide)
  have i58 : x^58≤x^59 := pow_le_pow_right₀ x1 (by decide)
  have i0 : 1≤x^59 := one_le_pow₀ x1
  have allowance := mul_le_mul_of_nonneg_right cut (pow_nonneg xn 59)
  have bet := mul_le_mul_of_nonneg_right b2 (pow_nonneg xn 40)
  have upper : E≤(5*beta/4+δ)*x^60 := by nlinarith only [size,allowance,i40,i45,i58,i0,bet]
  have scaled := pow_le_pow_left₀ ep upper 10
  have factor : x^600=8*n^3 := by calc
    x^600=(x^200)^3 := by ring
    _=_ := by rw [nx]; ring
  calc
    E^10 ≤ ((5*beta/4+δ)*x^60)^10 := scaled
    _ = (5*beta/4+δ)^10*x^600 := by ring
    _ = _ := by rw [factor]; ring

theorem coefficient {beta : ℝ} (b : beta^5=8) :
    2048*(8*(5*beta/4)^10)=9765625 := by
  have eq := congrArg (fun x : ℝ => x^2) b
  nlinarith only [eq]

#print axioms condition
#print axioms endpoint
#print axioms coefficient
end ThresholdUpperScalarRate
