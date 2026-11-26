import ExactPlaneConcreteSampler
import ExactPlaneOntoReadSpan
namespace ExactPlaneCoordinateSampler
open ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneSamplerRank
theorem all_coordinates (J : Type*) [Fintype J] [DecidableEq J] (R : Nat) :
    ∃ S : Finset (Vec J),S.card≤max 1 ((2*Fintype.card J*2^R)^2) ∧ OntoHits S R := by
  classical
  obtain ⟨T,cost,samples⟩ := ExactPlaneConcreteSampler.all_dimensions (Fintype.card J) R
  let e : Vec (Fin (Fintype.card J)) ≃ₗ[F] Vec J := LinearEquiv.funCongrLeft F F (Fintype.equivFin J)
  refine ⟨T.image e,Finset.card_image_le.trans cost,?_⟩
  intro k hk f sur y
  obtain ⟨s,hs,eq⟩ := samples k hk (f.comp e.toLinearMap) (sur.comp e.surjective) y
  exact ⟨e s,Finset.mem_image.mpr ⟨s,hs,rfl⟩,eq⟩
#print axioms all_coordinates
end ExactPlaneCoordinateSampler
