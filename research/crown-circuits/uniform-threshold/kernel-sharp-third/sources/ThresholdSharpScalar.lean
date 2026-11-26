import ThresholdThirdPower
namespace ThresholdSharpScalar

theorem maximum (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    3125*x*y^4≤256*(x+y)^5 := by
  have identity : 256*(x+y)^5-3125*x*y^4 =
      (4*x-y)^2*(16*x^3+88*x^2*y+203*x*y^2+256*y^3) := by ring
  have non : 0≤(4*x-y)^2*(16*x^3+88*x^2*y+203*x*y^2+256*y^3) := by positivity
  linarith

theorem unit_maximum (z : ℝ) (hz : 0≤z) (ho : z≤1) :
    z*(1-z)^4≤256/3125 := by
  have q := maximum z (1-z) hz (by linarith)
  rw [show z+(1-z)=1 by ring] at q
  norm_num at q ⊢
  linarith

/-- Two distinct additive errors are allowed; the unperturbed share may exceed one. -/
theorem perturbed (z a b d E h : ℝ) (hx : 0≤z+a) (hy : 0≤1-z+b)
    (he : 0≤E) (loss : (2-d)*h^3≤(z+a)*(1-z+b)^4*E^5) :
    3125*(2-d)*h^3≤256*(1+a+b)^5*E^5 := by
  have q := maximum (z+a) (1-z+b) hx hy
  rw [show z+a+(1-z+b)=1+a+b by ring] at q
  have mq := mul_le_mul_of_nonneg_right q (pow_nonneg he 5)
  linarith only [mq,loss]

#print axioms maximum
#print axioms unit_maximum
#print axioms perturbed
end ThresholdSharpScalar
