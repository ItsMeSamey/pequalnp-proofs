import ExactPlaneProfileSlice
import ExactPlaneProfileResidual
import ExactPlaneSectionComplement
import ExactPlaneMatchedBasis
namespace ExactPlaneProfileBranch
open ExactPlaneSuppliedCoordinates ExactPlanePhysicalConverse ExactPlaneResidualPivots
open ExactPlaneObservedSpan ExactPlaneProfileCharts ExactPlaneProfileResidual
open ExactPlanePhysicalResidual (residual)
open ExactPlaneDeterminantProfile (profile augmented)
open scoped BigOperators
variable {r d N : ℕ}
abbrev F := ZMod 2

structure Sections (p : Fin N→Key d) (b h : Fin N→Plane) (f : Heights d r) where
  dir : Fin r→ observed p
  independent : LinearIndependent F dir
  sites : X d→Fin r→Finset (Fin N)
  inside : ∀ x j,sites x j⊆active p b x
  privSum : ∀ x j,∑ i∈sites x j,key p i=dir j
  heightSum : ∀ x j,∑ i∈sites x j,h i=val f x j

theorem old_pivots {K : Type*} [AddCommGroup K] [Module F K] (k : Fin N→K) (b h : Fin N→Plane)
    (A : Finset (Fin N)) (trace : ExactTrace k b h A) (L : K→ₗ[F] Plane) :
    ∃ e∈A, ∃ z∈A, Independent (residual k h L e) (residual k h L z) := by
  classical
  let T := Submodule.span F ((residual k h L) '' (A:Set (Fin N)))
  obtain ⟨_,_,all⟩ := active_relations k b h A trace
  have whole (v : Plane) : v∈T := by
    obtain ⟨a,_,_,eq⟩ := all L v
    rw [←eq]
    exact T.sum_mem fun i _=>T.smul_mem _ (Submodule.subset_span ⟨i.val,i.property,rfl⟩)
  exact pivots A (residual k h L) (whole (1,0)) (whole (0,1)) ((det_ne_iff _ _).mp (by decide))

def branchSites (idx : Fin t→Fin N) (e z : Fin N) : Fin (t+2)→Fin N :=
  Fin.addCases idx ![e,z]

theorem sampled (p : Fin N→Key d) (b h : Fin N→Plane) (f : Heights d r)
    (s : Sections p b h f) (A : Finset (Fin N)) (tr : ExactTrace p b h A) :
    let t := Module.finrank F (observed p)-r
    ∃ l∈ExactPlaneDegreeSampler.ordered (ExactPlaneNumericalRows.points
      (ExactPlaneConstructedRows.generate (d+d) (2*(t+2)+1))) (profile (augmented f)),
      ExactTrace p b h (active p b l.sum) := by
  classical
  let t := Module.finrank F (observed p)-r
  have tr' := (trace_iff p b h A).mpr tr
  obtain ⟨g₀,ma⟩ := ExactPlanePhysicalConverse.chart (key p) b h A tr'
  obtain ⟨g,S,sub,ms,sp⟩ := ExactPlaneMatchedBasis.extend_matches (key p) b A g₀ ma (full p)
  obtain ⟨idx,B,_,ins,left,right⟩ := ExactPlaneSectionComplement.indexed (key p) S sp s.dir s.independent
  obtain ⟨x₀,hx⟩ := onto p g
  let c := fun j:Fin t=>h (idx j)
  let L := fun x:X d=>lift B f c x
  obtain ⟨e,he,z,hz,ind⟩ := old_pivots (key p) b h A tr' (L x₀)
  let sc :=  ExactPlaneProfileResidual.score B f c (key p e) (key p z) (h e) (h z)
  have nz : ExactPlaneSubsetPolynomial.eval sc (ExactPlaneAffineSpanHit.support x₀)≠0 := by
    dsimp only [sc]
    rw [score_eval]
    exact (det_ne_iff _ _).mpr ind
  obtain ⟨l,inside,same,win⟩ := sample_slice p (branchSites idx e z) x₀ sc (score_degree _ _ _ _ _ _ _) nz
  refine ⟨l,inside,(trace_iff p b h _).mp ?_⟩
  have transfer (j : Fin (t+2)) (sj : branchSites idx e z j ∈ S) :
      branchSites idx e z j ∈ active p b l.sum := by
    apply (mem_active _ _ _ _).mpr
    rw [←table_chart,same j,table_chart,hx]
    exact ms _ sj
  have anchor (q:Fin t) : idx q∈active p b l.sum := by
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
  apply (ExactPlaneSectionGraph.mixed_pivots _ (key p) b h (onObserved p l.sum) (L l.sum)
    (fun i hi=>((mem_active _ _ _ _).mp hi).symm) B (s.sites l.sum) idx (s.inside l.sum)
    (fun j=>(s.privSum _ j).trans (left j).symm) _ anchor (fun q=>(right q).symm) _).mpr
  · refine ⟨e,pivotE,z,pivotZ,(det_ne_iff _ _).mp ?_⟩
    dsimp only [sc] at win
    rwa [score_eval] at win
  · intro j
    simpa [L,lift] using s.heightSum l.sum j
  · intro j
    simp [L,lift,c]
end ExactPlaneProfileBranch
