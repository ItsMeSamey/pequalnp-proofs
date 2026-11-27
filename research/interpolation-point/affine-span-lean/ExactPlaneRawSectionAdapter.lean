import ExactPlaneRawSectionCheck
import ExactPlaneProfileSolver
namespace ExactPlaneRawSectionAdapter
open ExactPlaneRawSectionCheck ExactPlaneSparseSections ExactPlaneProfileSolver ExactPlaneProfileBranch
open ExactPlaneSuppliedCoordinates ExactPlaneObservedSpan ExactPlaneResidualPivots
open ExactPlaneProfileCharts ExactPlaneAffineSpanHit
open scoped BigOperators
variable {d r N : ℕ}

noncomputable def sections_of_valid {p : Fin N→Key d} {b : Fin N→Plane} {s : Selectors d r N}
    (h : Fin N→Plane) (ok : valid p b s=true) : Sections p b h (polynomials s h) := by
  obtain ⟨ind,validRows⟩ := valid_sound ok
  let lift (j : Fin r) : observed p :=
    ⟨direction p s j,by
      rw [←(validRows (0 : X d) j).2]
      exact (observed p).sum_mem fun i _=>(key p i).property⟩
  refine { dir := lift
           independent := LinearIndependent.of_comp (observed p).subtype ind
           sites := fun x j=>chosen (s j) (support x)
           inside := fun x j=>(validRows x j).1
           privSum := ?_
           heightSum := ?_ }
  · intro x j
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (validRows x j).2
  · intro x j
    exact eval_pair s h j (support x)

#print axioms sections_of_valid
end ExactPlaneRawSectionAdapter
