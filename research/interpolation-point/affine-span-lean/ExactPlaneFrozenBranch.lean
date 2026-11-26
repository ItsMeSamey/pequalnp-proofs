import ExactPlaneIndexedBranch
import ExactPlaneChartCoordinates
import ExactPlanePhysicalConverse
namespace ExactPlaneIndexedBranch
open Module ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneRepresentativeLookup
open ExactPlaneLookupDeterminant ExactPlaneSamplerRank ExactPlaneResidualPivots
open scoped BigOperators
variable {I K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup K] [Module F K] {N : ℕ}
variable {B : Basis I F K} {priv : Fin N→K} {tag : Fin N→Plane}

theorem initial_pivots (s : Selection B priv tag) (height : Fin N→Plane) (A : Finset (Fin N))
    (trace : ExactPlanePhysicalConverse.ExactTrace priv tag height A) (x : Vec (I×Bool)) :
    ∃ e∈A,∃ f∈A, Independent (res s height x e) (res s height x f) := by
  classical
  let L := lift s height x
  let G := Submodule.span F ((res s height x) '' (A:Set (Fin N)))
  have all (v : Plane) : v∈G := by
    obtain ⟨c,zero,_,value⟩ := ExactPlanePhysicalConverse.gain_relations priv tag height A trace v
    have lin := congrArg L zero
    simp only [map_sum,map_smul,map_zero] at lin
    have eq : (∑ i : ↥A,c i • res s height x i.val)=v := by
      simp only [res,smul_add,Finset.sum_add_distrib,value]
      change v + (∑ i : ↥A,c i • L (priv i.val))=v
      rw [lin,add_zero]
    rw [←eq]
    exact G.sum_mem (fun i _=>G.smul_mem _ (Submodule.subset_span ⟨i.val,i.property,rfl⟩))
  exact pivots A (res s height x) (all (1,0)) (all (0,1))
    ((det_ne_iff _ _).mp (by decide))

def Success (s : Selection B priv tag) (height : Fin N→Plane) (y : Vec (I×Bool)) : Prop :=
  s.Eligible y ∧ ∃ (U : Fin 2→Finset (Fin N)) (gains : Fin 2→Plane), LinearIndependent F gains ∧
      (∀ j,U j⊆active B priv tag y) ∧
      (∀ j,∑ i∈U j,ExactPlanePhysicalResidual.col priv tag height i=(0,0,gains j)) ∧ U 0≠U 1

theorem on_branch (s : Selection B priv tag) (height : Fin N→Plane) (A : Finset (Fin N))
    (trace : ExactPlanePhysicalConverse.ExactTrace priv tag height A)
    (g : K→ₗ[F] Plane) (matchA : ∀ i∈A,g (priv i)=tag i)
    (anchor : ∀ i hi,tag (s.anchor i hi)=g (priv (s.anchor i hi)))
    (S : Finset (Vec (I×Bool))) (sampling : OntoHits S (2*(Fintype.card (Partial s)+2)+1)) :
    ∃ l : List (Vec (I×Bool)),(∀ y∈l,y∈S) ∧ (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
      Success s height l.sum := by
  classical
  let x := coordinates B g
  have ok := eligible_coordinates s g anchor
  obtain ⟨e,he,f,hf,ind⟩ := initial_pivots s height A trace x
  let read := fun e side=>test B (priv e) side
  let t := fun e side=>component side (tag e)
  let a := fun j : Partial s => s.anchor j.val j.property
  have matched (i) (hi : i∈A) : ExactPlanePinnedSampling.Matched read t x i := by
    apply (row_iff x i).mpr
    change tag i=tagChart B (coordinates B g) (priv i)
    rw [chart_coordinates]; exact (matchA i hi).symm
  obtain ⟨l,inside,len,keep,ee,ff,hot⟩ := ExactPlanePinnedSampling.sample S sampling a read t e f
    (code s height e false) (code s height f false) (code s height e true) (code s height f true)
    x (fun j=>(row_iff x _).mpr ((anchor_iff s x).mp ok j)) (matched e he) (matched f hf)
    ((code_ind s height e f x).mpr ind)
  have valid := (anchor_iff s l.sum).mpr (fun j=>(row_iff l.sum _).mp (keep j))
  exact ⟨l,fun y hy=>(inside y hy).1,len,valid,final_support s height _ valid e f
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(row_iff _ e).mp ee⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(row_iff _ f).mp ff⟩)
    ((code_ind s height e f _).mp hot)⟩
#print axioms on_branch
end ExactPlaneIndexedBranch
