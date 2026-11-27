import ExactPlaneDeterminantProfile
import ExactPlaneTwoBitLookup

namespace ExactPlaneDeterminantProfile
open ExactPlaneSubsetPolynomial ExactPlaneAffineSubstitution
variable {J G : Type*} [Fintype J] [DecidableEq J] [Fintype G]

/-- Independent truth tables for both coordinates may share both affine inputs. -/
theorem lookup_profile (left right : G → F × F → F) (x y : G → Coeff J)
    (hx : ∀ i,degreeLE 1 (x i)) (hy : ∀ i,degreeLE 1 (y i)) :
    ∃ f : G → Pair J,
      (∀ i A,eval (f i).1 A=left i (eval (x i) A,eval (y i) A)) ∧
      (∀ i A,eval (f i).2 A=right i (eval (x i) A,eval (y i) A)) ∧
      profile (augmented f)≤4 := by
  classical
  choose p dp ep using fun i => ExactPlaneTwoBitLookup.lookup_affine (left i) (x i) (y i) (hx i) (hy i)
  choose q dq eq using fun i => ExactPlaneTwoBitLookup.lookup_affine (right i) (x i) (y i) (hx i) (hy i)
  exact ⟨fun i => (p i,q i),ep,eq,augmented_coordinates (fun i => (p i,q i)) dp dq⟩

#print axioms lookup_profile
end ExactPlaneDeterminantProfile
