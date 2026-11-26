import ThresholdSharpScalar
namespace ThresholdSharpAggregate

/-- S=A+D; A denotes adjacent codegree mass, D nonadjacent mass.
F is the total relevant loss (missing plus competing cold pairs only). -/
theorem wedge_loss (h w g S A D F eta lam : ℝ) (hw : 0≤w)
    (etaBound : eta≤2) (sums : S=A+D)
    (wedges : 2*g^2≤w*(S+g))
    (rowError : 2*h^2-2*g^2+w*(g+A)≤eta*h^2)
    (diagError : D*w^4≤lam*h^4)
    (moment : 2*D^2≤w^2*(4*F+D)) :
    ((2-eta)^2/2-lam/4)*h^4≤F*w^4 := by
  rw [sums] at wedges
  have base : (2-eta)*h^2≤w*D := by nlinarith only [wedges,rowError]
  have pos : 0≤(2-eta)*h^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have square := pow_le_pow_left₀ pos base 2
  have moment' := mul_le_mul_of_nonneg_right moment (sq_nonneg w)
  nlinarith only [square,moment',diagError]

/-- Combine physical column budget and wedge loss without dividing by column count. -/
theorem aggregate (h E w F z a b eta lam : ℝ) (hh : 0<h) (he : 0≤E)
    (hw : 0≤w) (hF : 0≤F) (hx : 0≤z+a) (hy : 0≤1-z+b)
    (rowLoss : ((2-eta)^2/2-lam/4)*h^4≤F*w^4)
    (charged : F≤(z+a)*h*E) (columns : w≤(1-z+b)*E) :
    3125*((2-eta)^2/2-lam/4)*h^3≤256*(1+a+b)^5*E^5 := by
  have weight := pow_le_pow_left₀ hw columns 4
  have step := mul_le_mul_of_nonneg_left weight hF
  have next := mul_le_mul_of_nonneg_right charged (pow_nonneg (mul_nonneg hy he) 4)
  have both : h*(((2-eta)^2/2-lam/4)*h^3) ≤
      h*((z+a)*(1-z+b)^4*E^5) := by nlinarith only [rowLoss,step,next]
  have divided := (mul_le_mul_iff_right₀ hh).mp both
  have d := ThresholdSharpScalar.perturbed z a b (2-((2-eta)^2/2-lam/4)) E h hx hy he
  apply (by simpa only [sub_sub_cancel] using d)
  exact divided

#print axioms wedge_loss
#print axioms aggregate
end ThresholdSharpAggregate
