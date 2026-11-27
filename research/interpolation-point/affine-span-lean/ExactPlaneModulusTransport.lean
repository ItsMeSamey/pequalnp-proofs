import ExactPlaneBinaryArithmetic
namespace ExactPlaneBinaryArithmetic
variable {P : Polynomial F} {r : ℕ}

noncomputable def wordEquiv (hm : P.Monic) (deg : P.natDegree = r) :
    Word r ≃ₗ[F] AdjoinRoot P := deg ▸ encode hm

theorem wordEquiv_power (hm : P.Monic) (deg : P.natDegree = r) (hr : 0 < r)
    (c : Word r) (coeff : ∀ i : Fin r,c i = -P.coeff i.val) (x : Word r) (n : ℕ) :
    wordEquiv hm deg (power c x n) = wordEquiv hm deg x ^ n := by
  subst r
  have eq : c = fun i => -P.coeff i.val := funext coeff
  rw [eq]
  exact encode_power hm hr x n

#print axioms wordEquiv_power
end ExactPlaneBinaryArithmetic
