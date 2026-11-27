import ExactPlaneCheckedProfile
import ExactPlaneSectionCheckComplete
namespace ExactPlaneCheckedProfile
open ExactPlaneProfileSolver (Selectors)
open ExactPlaneSuppliedCoordinates (Key)
open ExactPlaneProfileCharts (X active)
open ExactPlaneAffineSpanHit (support)
open ExactPlaneSparseSections (chosen)
open ExactPlaneResidualPivots (Plane)
variable {N d r : Nat}

theorem supported_path (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane)
    (u : Fin r→Key d) (li : LinearIndependent (ZMod 2) u)
    (physical : ∀ x : X d,∀ j, chosen (s j) (support x) ⊆ active p b x ∧
      (∑ i∈chosen (s j) (support x),p i)=u j) :
    solve s p b h = ExactPlaneProfileSolver.solve s p b h :=
  valid_path ((ExactPlaneSectionCheckComplete.valid_iff_phys p b s).mpr ⟨u,li,physical⟩)
#print axioms supported_path
end ExactPlaneCheckedProfile
