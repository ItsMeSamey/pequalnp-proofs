import ThresholdSharpGlobalLower
namespace ThresholdSharpGlobalLower
theorem regular_margin {m E t u : ℝ} (mn : 0≤m) (en : 0≤E) (tn : 0≤t)
    (sq : t^2=2*m) (un : 0≤u) (small : u≤1/1000)
    (ledger : 3125*((2-u)^2/2-u/4)*(1-u)^3*t^3≤256*(1+2*u)^5*E^5) :
    (1-1000*u)*coeff*m^3≤E^10 := by
  have cub : 1-3*u≤(1-u)^3 := by nlinarith [mul_nonneg (sq_nonneg u) (show 0≤3-u by linarith)]
  have bracket : 2*(1-2*u)≤(2-u)^2/2-u/4 := by nlinarith [sq_nonneg u]
  have mult := mul_le_mul bracket cub (by linarith : 0≤1-3*u)
      (by nlinarith [sq_nonneg u] : 0≤(2-u)^2/2-u/4)
  have num : 2*(1-5*u)≤((2-u)^2/2-u/4)*(1-u)^3 := by nlinarith only [mult,sq_nonneg u]
  have u2 : u^2≤u := by nlinarith [mul_nonneg un (show 0≤1-u by linarith)]
  have u3 : u^3≤u := by nlinarith [mul_le_mul_of_nonneg_right u2 un]
  have u4 : u^4≤u := by nlinarith [mul_le_mul_of_nonneg_right u3 un]
  have u5 : u^5≤u := by nlinarith [mul_le_mul_of_nonneg_right u4 un]
  have den : (1+2*u)^5≤1+242*u := by nlinarith only [u2,u3,u4,u5]
  have cross : (1-247*u)*(1+242*u)≤1-5*u := by nlinarith [sq_nonneg u]
  have cp := mul_le_mul_of_nonneg_right cross (pow_nonneg tn 3)
  have np := mul_le_mul_of_nonneg_right num (pow_nonneg tn 3)
  have dp := mul_le_mul_of_nonneg_right den (pow_nonneg en 5)
  have pre : (1+242*u)*(6250*(1-247*u)*t^3)≤(1+242*u)*(256*E^5) := by
    nlinarith only [ledger,cp,np,dp]
  have five := (mul_le_mul_iff_right₀ (show 0<1+242*u by linarith)).mp pre
  have power := pow_le_pow_left₀ (mul_nonneg (by linarith : 0≤6250*(1-247*u)) (pow_nonneg tn 3)) five 2
  have ts : t^6=8*m^3 := by calc
    t^6=(t^2)^3 := by ring
    _=_ := by rw [sq]; ring
  have paid : 1-1000*u≤(1-247*u)^2 := by nlinarith [sq_nonneg u]
  have scaled := mul_le_mul_of_nonneg_right paid (pow_nonneg mn 3)
  have id : (6250*(1-247*u)*t^3)^2=6250^2*(1-247*u)^2*(8*m^3) := by
    rw [←ts]; ring
  rw [id] at power
  unfold coeff
  nlinarith only [power,scaled]

#print axioms regular_margin
end ThresholdSharpGlobalLower
