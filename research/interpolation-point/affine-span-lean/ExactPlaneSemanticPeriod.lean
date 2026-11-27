import ExactPlaneCheckedPeriod
import ExactPlaneSectionCheckComplete
namespace ExactPlaneCheckedPeriod
open ExactPlaneProfileSolver (Selectors polynomials)
open ExactPlaneSuppliedCoordinates (Key)
open ExactPlaneResidualPivots (Plane)
open ExactPlaneSparseSections (chosen)
open ExactPlaneAffineSpanHit (support)
open ExactPlaneProfileCharts (X active)

theorem physical_path {v : Fin a→X d} {s : Selectors d r N} {p : Fin N→Key d} {b h : Fin N→Plane}
    (u : Fin r→Key d) (ind : LinearIndependent (ZMod 2) u)
    (secs : ∀ x : X d,∀ j, chosen (s j) (support x)⊆active p b x ∧
      (∑ i∈chosen (s j) (support x),p i)=u j)
    (periods : ∀ x y : X d,x-y∈ExactPlaneSuppliedPeriods.W v → ∀ j,
      (∑ i∈chosen (s j) (support x),h i)=(∑ i∈chosen (s j) (support y),h i)) :
    solve v s p b h =
      if usePeriod v s p h then ExactPlaneRawPeriod.solve v s p b h
      else ExactPlaneProfileSolver.solve s p b h := by
  apply valid_path ((ExactPlaneSectionCheckComplete.valid_iff_phys p b s).mpr ⟨u,ind,secs⟩)
  apply (ExactPlaneSuppliedPeriods.valid_iff s h v).mpr
  intro x y diff j
  exact (ExactPlaneSparseSections.eval_pair s h j (support x)).symm.trans
    ((periods x y diff j).trans (ExactPlaneSparseSections.eval_pair s h j (support y)))
#print axioms physical_path
end ExactPlaneCheckedPeriod
