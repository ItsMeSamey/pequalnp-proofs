import ExactPlanePeriodSlice
import ExactPlaneProfileBranch
namespace ExactPlanePeriodBranch
open ExactPlaneProfileBranch ExactPlaneSuppliedCoordinates ExactPlanePhysicalConverse ExactPlaneResidualPivots
open ExactPlaneObservedSpan ExactPlaneProfileCharts ExactPlaneProfileResidual
open ExactPlanePhysicalResidual (residual)
open ExactPlaneConstructedRows ExactPlaneNumericalRows
variable {d r N : Nat}
theorem sampled_periods (p : Fin N→Key d) (b h : Fin N→Plane) (f : Heights d r)
    (s : Sections p b h f) (W : Submodule (ZMod 2) (X d))
    (invariant : ∀ x y : X d,x-y∈W → ∀j,val f x j=val f y j)
    (A : Finset (Fin N)) (tr : ExactTrace p b h A) :
    let t := Module.finrank (ZMod 2) (observed p)-r
    ∃ x∈points (generate (d+d) (Module.finrank (ZMod 2) ((X d) ⧸ W)+2*(t+2))),
      ExactTrace p b h (active p b x) := by
  classical
  let t := Module.finrank (ZMod 2) (observed p)-r
  have tr' := (trace_iff p b h A).mpr tr
  obtain ⟨g₀,ma⟩ := ExactPlanePhysicalConverse.chart (key p) b h A tr'
  obtain ⟨g,S,sub,ms,sp⟩ := ExactPlaneMatchedBasis.extend_matches (key p) b A g₀ ma (full p)
  obtain ⟨idx,B,_,ins,left,right⟩ := ExactPlaneSectionComplement.indexed (key p) S sp s.dir s.independent
  obtain ⟨x₀,hx⟩ := onto p g
  let c := fun j:Fin t=>h (idx j)
  let L := fun x:X d=>lift B f c x
  obtain ⟨e,he,z,hz,ind⟩ := old_pivots (key p) b h A tr' (L x₀)
  obtain ⟨x,inside,per,same⟩ := ExactPlanePeriodSlice.period_sites W p (branchSites idx e z) x₀
  have sameVal : val f x₀=val f x := funext fun j => (invariant x x₀ per j).symm
  have sameL : L x₀=L x := by simp only [L,lift,sameVal]
  refine ⟨x,inside,(trace_iff p b h _).mp ?_⟩
  have transfer (j : Fin (t+2)) (sj : branchSites idx e z j ∈ S) :
      branchSites idx e z j ∈ active p b x := by
    apply (mem_active _ _ _ _).mpr
    rw [←table_chart,same j,table_chart,hx]
    exact ms _ sj
  have anchor (q:Fin t) : idx q∈active p b x := by
    simpa only [branchSites,Fin.addCases_left] using transfer (Fin.castAdd 2 q)
      (by simpa only [branchSites,Fin.addCases_left] using ins q)
  have tail (j : Fin 2) : branchSites idx e z (Fin.natAdd t j) = ![e,z] j := by
    exact Fin.addCases_right (motive := fun _ : Fin (t+2) => Fin N) (left:=idx) (right:=![e,z]) j
  have ez : branchSites idx e z (Fin.natAdd t 0)=e := tail 0
  have zz : branchSites idx e z (Fin.natAdd t 1)=z := tail 1
  have pivotE := transfer (Fin.natAdd t 0) (ez.symm ▸ sub he)
  have pivotZ := transfer (Fin.natAdd t 1) (zz.symm ▸ sub hz)
  rw [ez] at pivotE
  rw [zz] at pivotZ
  apply (ExactPlaneSectionGraph.mixed_pivots _ (key p) b h (onObserved p x) (L x)
    (fun i hi=>((mem_active _ _ _ _).mp hi).symm) B (s.sites x) idx (s.inside x)
    (fun j=>(s.privSum _ j).trans (left j).symm) _ anchor (fun q=>(right q).symm) _).mpr
  · exact ⟨e,pivotE,z,pivotZ,by simpa only [sameL] using ind⟩
  · intro j
    simpa [L,lift] using s.heightSum x j
  · intro j
    simp [L,lift,c]
#print axioms sampled_periods
end ExactPlanePeriodBranch
