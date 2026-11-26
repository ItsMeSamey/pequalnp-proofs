import ExactPlaneSamplerSpan
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
namespace ExactPlaneSamplerRank
open ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneSamplerSpan
variable {J : Type*} [Fintype J] [DecidableEq J]

def OntoHits (seed : Finset (Vec J)) (R : Nat) : Prop :=
  ∀ k≤R, ∀ f : Vec J →ₗ[F] (Fin k→F), Function.Surjective f →
    ∀ y,∃ s∈seed,f s=y

theorem hits_of_onto {seed : Finset (Vec J)} {R : Nat} (onto : OntoHits seed R) :
    Hits seed R := by
  classical
  intro k hk read x
  let f := LinearMap.pi read
  let r := Module.finrank F (LinearMap.range f)
  let e := (Module.finBasis F (LinearMap.range f)).equivFun
  let q : Vec J →ₗ[F] (Fin r→F) := e.toLinearMap.comp f.rangeRestrict
  have rk : r≤k := by
    have le : Module.finrank F (LinearMap.range f)≤Module.finrank F (Fin k→F) :=
      Submodule.finrank_le _
    simpa only [Module.finrank_pi,Fintype.card_fin] using le
  have sur : Function.Surjective q := e.surjective.comp f.surjective_rangeRestrict
  obtain ⟨s,hs,eq⟩ := onto r (rk.trans hk) q sur (q x)
  have same : f.rangeRestrict s=f.rangeRestrict x := e.injective eq
  have val : f s=f x := congrArg Subtype.val same
  exact ⟨s,hs,fun i => congrFun val i⟩
#print axioms hits_of_onto
end ExactPlaneSamplerRank
