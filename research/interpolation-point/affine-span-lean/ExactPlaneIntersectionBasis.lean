import ExactPlaneIntersectionKernel
import ExactPlaneFeatureStream
import Mathlib.Data.Fin.Tuple.Basic
namespace ExactPlaneIntersectionBasis
open ExactPlaneGaussian ExactPlaneIntersectionKernel Submodule
open private normal reduce_val from ExactPlaneGaussian
variable {d n : ℕ}
abbrev space (v : Fin n → V d) (ids : List (Fin n)) := span F (v '' (ids.toFinset : Set (Fin n)))

def residualMap (v : Fin n → V d) (ids : List (Fin n)) : V d →ₗ[F] V d :=
  (LinearMap.fst F _ _).comp ((reduceMap (build v ids)).comp (LinearMap.inl F _ _))

theorem residual_zero (v : Fin n → V d) (ids : List (Fin n)) (x : V d) :
    residualMap v ids x=0 ↔ x∈space v ids := by
  unfold space
  rw [←build_span]
  change (reduce (build v ids) (x,0)).1=0 ↔ normal (build v ids) x=0
  rw [reduce_val]

def combined (v : Fin n → V d) (l r : List (Fin n)) : V d →ₗ[F] V (d+d) :=
  LinearMap.pi (Fin.addCases (fun i => (LinearMap.proj i).comp (residualMap v l))
    (fun i => (LinearMap.proj i).comp (residualMap v r)))

theorem ker_combined (v : Fin n → V d) (l r : List (Fin n)) :
    LinearMap.ker (combined v l r)=space v l ⊓ space v r := by
  ext x
  change combined v l r x=0 ↔ x ∈ space v l ∧ x ∈ space v r
  rw [←residual_zero,←residual_zero]
  constructor
  · intro zero
    exact ⟨funext (fun i => by simpa only [combined,LinearMap.pi_apply,Fin.addCases_left,Fin.addCases_right,LinearMap.comp_apply,LinearMap.proj_apply,Pi.zero_apply] using congrFun zero (Fin.castAdd d i)),
      funext (fun i => by simpa only [combined,LinearMap.pi_apply,Fin.addCases_left,Fin.addCases_right,LinearMap.comp_apply,LinearMap.proj_apply,Pi.zero_apply] using congrFun zero (Fin.natAdd d i))⟩
  · rintro ⟨a,b⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [combined,LinearMap.pi_apply,Fin.addCases_left,Fin.addCases_right,LinearMap.comp_apply,LinearMap.proj_apply,Pi.zero_apply] using congrFun a j
    · simpa only [combined,LinearMap.pi_apply,Fin.addCases_left,Fin.addCases_right,LinearMap.comp_apply,LinearMap.proj_apply,Pi.zero_apply] using congrFun b j

def basisRows (v : Fin n → V d) (l r : List (Fin n)) : List (V d) :=
  let H := combined v l r
  ExactPlaneFeatureStream.select Vector.ofFn ((List.finRange d).map (generators H))

theorem basisRows_spec (v : Fin n → V d) (l r : List (Fin n)) :
    let xs := basisRows v l r
    xs.Nodup ∧ LinearIndepOn F id (ExactPlaneFeatureStream.sites xs) ∧
      span F (ExactPlaneFeatureStream.sites xs)=space v l ⊓ space v r ∧ xs.length≤d := by
  let H := combined v l r
  let ys := (List.finRange d).map (generators H)
  obtain ⟨_,nd,ind,eq,lim⟩ := ExactPlaneFeatureStream.select_spec (fun x : V d => Vector.ofFn x) ys
  have coords : ExactPlaneFeatureStream.features (fun x : V d => Vector.ofFn x)=id := by
    funext x i
    simp [ExactPlaneFeatureStream.features]
  rw [coords] at ind eq
  simp only [Set.image_id] at eq
  have base : ExactPlaneFeatureStream.sites ys=Set.range (generators H) := by
    ext x
    simp [ys,ExactPlaneFeatureStream.sites]
  exact ⟨nd,ind,eq.trans ((congrArg (span F) base).trans ((span_generators H).trans (ker_combined _ _ _))),lim⟩

#print axioms basisRows_spec
end ExactPlaneIntersectionBasis
