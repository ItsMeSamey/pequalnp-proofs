import ExactPlaneRepresentativeLookup
namespace ExactPlaneRepresentativeLookup
open ExactPlaneAffineSpanHit ExactPlaneAffineSubstitution Module
variable {I K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup K] [Module F K]
noncomputable def coordinates (B : Basis I F K) (g : K →ₗ[F] F × F) : Vec (I × Bool) :=
  fun j => component j.2 (g (B j.1))

theorem coordinates_target (B : Basis I F K) (g : K →ₗ[F] F × F) (i : I) :
    target (coordinates B g) i = g (B i) := by
  exact Prod.ext rfl rfl

theorem chart_coordinates (B : Basis I F K) (g : K →ₗ[F] F × F) :
    tagChart B (coordinates B g) = g := by
  apply B.ext
  intro i
  simpa only [tagChart,Basis.constr_basis] using coordinates_target B g i

variable {N : ℕ} {B : Basis I F K} {priv : Fin N → K} {tag : Fin N → F × F}
theorem eligible_coordinates (s : Selection B priv tag) (g : K →ₗ[F] F × F)
    (matchAnchor : ∀ i hi, tag (s.anchor i hi) = g (priv (s.anchor i hi))) :
    s.Eligible (coordinates B g) := by
  intro i hi
  rw [coordinates_target, ← s.anchor_key i hi]
  exact matchAnchor i hi

#print axioms chart_coordinates
#print axioms eligible_coordinates
end ExactPlaneRepresentativeLookup
