import ExactPlaneLookupDeterminant
import ExactPlaneActiveDeterminant
namespace ExactPlaneLookupDeterminant
open ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneActivationSlice ExactPlaneDeterminant
variable {J K T : Type*} [Fintype J] [DecidableEq J] [Fintype K]

/-- If the two lookup-derived residual columns span the binary plane somewhere
in the affine span of the active seeds, an odd sum of at most five active
seeds attains it in the same span and the same affine activation slice. -/
theorem active_read_span (seed : Finset (Vec J)) (read : T→Vec J →ₗ[F] F) (offset target : T→F)
    (a b c d : Residual J K)
    (hit : ∃ x∈affineSpan F (slice seed read offset target:Set (Vec J)),
      independent a.read b.read c.read d.read x) :
    ∃ l : List (Vec J),(∀ x∈l,x∈seed ∧ Active read offset target x) ∧
      (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
      l.sum∈affineSpan F (slice seed read offset target:Set (Vec J)) ∧
      Active read offset target l.sum ∧ independent a.read b.read c.read d.read l.sum :=
  ExactPlaneActiveDeterminant.active_span seed read offset target
    (residual_quadratic a) (residual_quadratic b) (residual_quadratic c) (residual_quadratic d) hit

#print axioms active_read_span
end ExactPlaneLookupDeterminant
