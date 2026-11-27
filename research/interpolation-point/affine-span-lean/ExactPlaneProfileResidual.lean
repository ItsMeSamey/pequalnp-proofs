import ExactPlaneDeterminantProfile
import ExactPlaneProfileCharts
import ExactPlaneSectionGraph
namespace ExactPlaneProfileResidual
open ExactPlaneAffineSubstitution (Coeff)
open ExactPlaneSubsetPolynomial (eval)
open ExactPlaneAffineSpanHit (support)
open ExactPlaneDeterminantProfile ExactPlaneResidualPivots ExactPlaneProfileCharts
open scoped BigOperators
abbrev F := ZMod 2
variable {d r t : ℕ} {K : Type*} [AddCommGroup K] [Module F K]
abbrev Heights (d r : ℕ) := Fin r→Pair (Fin (d+d))

noncomputable def val (f : Heights d r) (x : X d) (p : Fin r) : Plane :=
  (eval (f p).1 (support x),eval (f p).2 (support x))

noncomputable def lift (D : Module.Basis (Fin r ⊕ Fin t) F K) (f : Heights d r)
    (c : Fin t → Plane) (x : X d) : K →ₗ[F] Plane :=
  D.constr F (Sum.elim (val f x) c)

noncomputable def fixed (D : Module.Basis (Fin r ⊕ Fin t) F K) (c : Fin t→Plane) (k : K) (h : Plane) :=
  h+∑ i : Fin t,D.repr k (Sum.inr i) • c i

noncomputable def weights (D : Module.Basis (Fin r ⊕ Fin t) F K) (c : Fin t→Plane) (k : K) (h : Plane) :
    Fin r ⊕ Bool → F := Sum.elim (fun i=>D.repr k (Sum.inl i))
      (fun b=>if b then (fixed D c k h).2 else (fixed D c k h).1)

theorem value_combo (D : Module.Basis (Fin r ⊕ Fin t) F K) (f : Heights d r) (c : Fin t→Plane)
    (k : K) (h : Plane) (x : X d) :
    let v := combo (augmented f) (weights D c k h)
    (eval v.1 (support x), eval v.2 (support x)) = h + lift D f c x k := by
  classical
  dsimp only
  rw [lift,Module.Basis.constr_apply_fintype,Fintype.sum_sum_type]
  apply Prod.ext <;>
    simp [combo,eval_lc,Fintype.sum_sum_type,Fintype.sum_bool,weights,augmented,eval_const,
      val,fixed,Prod.fst_sum,Prod.snd_sum,smul_eq_mul,add_comm,add_left_comm,add_assoc]

noncomputable def score (D : Module.Basis (Fin r ⊕ Fin t) F K) (f : Heights d r) (c : Fin t→Plane)
    (ke kf : K) (he hf : Plane) : Coeff (Fin (d+d)) :=
  detANF (combo (augmented f) (weights D c ke he)) (combo (augmented f) (weights D c kf hf))

theorem score_degree (D : Module.Basis (Fin r ⊕ Fin t) F K) (f : Heights d r) (c : Fin t→Plane)
    (ke kf : K) (he hf : Plane) : ExactPlaneSubsetPolynomial.degreeLE (profile (augmented f))
      (score D f c ke kf he hf) := combination_degree _ _ _

theorem score_eval (D : Module.Basis (Fin r ⊕ Fin t) F K) (f : Heights d r) (c : Fin t→Plane)
    (ke kf : K) (he hf : Plane) (x : X d) :
    eval (score D f c ke kf he hf) (support x)=det (he+lift D f c x ke) (hf+lift D f c x kf) := by
  rw [←value_combo D f c ke he x,←value_combo D f c kf hf x]
  exact eval_det _ _ _
end ExactPlaneProfileResidual
