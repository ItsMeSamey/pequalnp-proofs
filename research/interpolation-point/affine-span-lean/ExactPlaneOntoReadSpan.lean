import ExactPlaneActiveReadSpan
import ExactPlaneSamplerRank
namespace ExactPlaneLookupDeterminant
open ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneActivationSlice ExactPlaneDeterminant
open ExactPlaneSamplerRank
variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]

/-- The witness premise uses the whole feasible slice. One spare sampler
equation suffices to recover the slice as the affine span of active seeds. -/
theorem onto_sampled_read_span (seed : Finset (Vec J)) (r : Nat) (sampling : OntoHits seed (r+1))
    (k : Nat) (hk : k≤r) (read : Fin k→Vec J →ₗ[F] F) (offset target : Fin k→F)
    (a b c d : Residual J K)
    (witness : ∃ x,Active read offset target x ∧ independent a.read b.read c.read d.read x) :
    ∃ l : List (Vec J),(∀ x∈l,x∈seed ∧ Active read offset target x) ∧
      (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
      l.sum∈affineSpan F (slice seed read offset target:Set (Vec J)) ∧
      Active read offset target l.sum ∧ independent a.read b.read c.read d.read l.sum := by
  obtain ⟨x,feasible,ind⟩ := witness
  apply active_read_span seed read offset target a b c d
  refine ⟨x,?_,ind⟩
  have cover := ExactPlaneSamplerSpan.span_slice seed r (hits_of_onto sampling) k hk read offset target
  change x∈(affineSpan F (slice seed read offset target:Set (Vec J)) : Set _)
  rw [cover]
  exact feasible
#print axioms onto_sampled_read_span
end ExactPlaneLookupDeterminant
