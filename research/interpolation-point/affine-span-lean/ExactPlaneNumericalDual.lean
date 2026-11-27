import ExactPlaneNumericalRows
namespace ExactPlaneNumericalRows
open ExactPlaneFieldSampler ExactPlaneSamplerRank

def dot (t : V r) : V r →ₗ[F] F where
  toFun x := ∑ i, x i*t i
  map_add' x y := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_assoc,Finset.mul_sum,smul_eq_mul]

theorem dot_onto (r : Nat) : Function.Surjective (dot (r:=r)) := by
  intro l
  refine ⟨fun i=>l (fun j=>if i=j then 1 else 0),?_⟩
  apply LinearMap.ext
  intro x
  symm
  rw [LinearMap.pi_apply_eq_sum_univ l x]
  rfl

def functional {K : Type*} [Field K] [Algebra F K] (e : V r ≃ₗ[F] K) (t : V r) : D K :=
  (dot t).comp e.symm.toLinearMap

theorem functional_onto {K : Type*} [Field K] [Algebra F K] (e : V r ≃ₗ[F] K) :
    Function.Surjective (functional e) := by
  intro l
  obtain ⟨t,h⟩ := dot_onto r (l.comp e.toLinearMap)
  refine ⟨t,?_⟩
  ext x
  simp [functional,h]

theorem power_hits {K : Type*} [Field K] [Algebra F K] [Fintype K] [Fintype (D K)]
    (e : V r ≃ₗ[F] K) (power : V r→Nat→V r) (ok : ∀ x j,e (power x j)=(e x)^j)
    (hm : 0<m) (large : m*2^R<Fintype.card K) :
    OntoHits (points (rows r m (fun x t j=>dot t (power x j.val)))).toFinset R := by
  apply hits r m R _ K e (functional e) e.surjective (functional_onto e) _ hm large
  intro x t j
  simp [functional,←ok]
end ExactPlaneNumericalRows
