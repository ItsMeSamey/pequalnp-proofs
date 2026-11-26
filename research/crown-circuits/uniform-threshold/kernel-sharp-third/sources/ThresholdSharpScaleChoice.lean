import ThresholdSharpScaleRelative
import ThresholdScaleRoot
namespace ThresholdSharpScaleBand

private theorem root_le_of_square {a y : ℝ} (sq : a^2≤y) (yp : 0≤y) :
    a≤Real.sqrt y := by
  by_contra! bad
  have lt := pow_lt_pow_left₀ bad (Real.sqrt_nonneg y) (by decide : (2:ℕ)≠0)
  rw [Real.sq_sqrt yp] at lt
  exact (not_lt_of_ge sq) lt

set_option maxRecDepth 8192

/-- Uniform choice for every terminal order beyond one cutoff that depends only on B,u. -/
theorem choose {B u : ℝ} (bp : 0<B) (up : 0<u) (us : u≤1/1000) :
    ∃ (P : ℝ) (N : ℕ), 14≤P ∧ B≤P ∧ (2:ℝ)^80≤P ∧
      (2:ℝ)^20≤(u/10)*P ∧ 1≤u*P ∧
      ∀ m : ℕ, N≤m → ∃ X : ℝ, P^100≤X ∧ X^10=Real.sqrt (2*(m:ℝ)) := by
  let P := (2:ℝ)^80*(1+B+1/u)
  have inv : 0≤u⁻¹ := by positivity
  have p80 : (2:ℝ)^80≤P := by dsimp [P]; norm_num; linarith
  have pp : 1≤P := by norm_num at p80; linarith
  have pB : B≤P := by dsimp [P]; norm_num; linarith
  have prod : (2:ℝ)^80≤u*P := by
    have cancel : u*(1/u)=1 := by field_simp
    dsimp [P]; nlinarith only [cancel,mul_nonneg up.le bp.le,up.le]
  have p14 : 14≤P := (by norm_num : (14:ℝ)≤2^80).trans p80
  have cost : (2:ℝ)^20≤(u/10)*P := by norm_num at prod ⊢; linarith only [prod]
  have unit : 1≤u*P := (by norm_num : (1:ℝ)≤2^80).trans prod
  obtain ⟨N,hN⟩ := exists_nat_ge (((P^100)^10)^2)
  refine ⟨P,N,p14,pB,p80,cost,unit,?_⟩
  intro m large
  have bigger : (N:ℝ)≤(m:ℝ) := by exact_mod_cast large
  have base : 1≤P^100 := one_le_pow₀ pp
  have nle : (m:ℝ)≤2*(m:ℝ) := by linarith only [Nat.cast_nonneg m (α:=ℝ)]
  have root : (P^100)^10≤Real.sqrt (2*(m:ℝ)) :=
    root_le_of_square (a:=(P^100)^10) (y:=2*(m:ℝ)) ((hN.trans bigger).trans nle)
      (mul_nonneg (by norm_num) (Nat.cast_nonneg m))
  exact ThresholdScaleRoot.exists_above (by decide : (10:ℕ)≠0) base root

/-- Pay the elementary hypotheses of budget using the same scale. -/
theorem budget_from_scale (t E K P X : ℝ) (xp : P≤X) (pp : (2:ℝ)^20≤P)
    (time : t=X^10) (low : X^6≤(2:ℝ)^16*E) (high : E≤P*X^6)
    (eq : 2*K=2*t*E+E^2+7*t+7*E+14) : 2*K≤4*t*E := by
  have xbig : (2:ℝ)^20≤X := pp.trans xp
  have x1 : 1≤X := by norm_num at xbig; linarith
  have xp6 : X≤X^6 := by simpa using (pow_le_pow_right₀ x1 (by decide : 1≤6))
  have xp10 : X≤X^10 := by simpa using (pow_le_pow_right₀ x1 (by decide : 1≤10))
  have elow : 14≤E := by norm_num at xbig low; linarith
  have four : 4≤X := by norm_num at xbig; linarith
  have xs : X^2≤X^4 := pow_le_pow_right₀ x1 (by decide)
  have pr : 4*P≤X^4 := by nlinarith [mul_le_mul_of_nonneg_right four (show 0≤X by linarith)]
  have scale := mul_le_mul_of_nonneg_right pr (pow_nonneg (show 0≤X by linarith) 6)
  have small : E≤t/4 := by rw [time]; nlinarith only [scale,high]
  exact budget t E K (by linarith) (by linarith) elow small (by linarith) eq

#print axioms choose
#print axioms budget_from_scale
end ThresholdSharpScaleBand
