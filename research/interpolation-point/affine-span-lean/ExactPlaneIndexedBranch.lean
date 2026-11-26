import ExactPlanePinnedSampling
import ExactPlaneRepresentativeLookup
import ExactPlanePhysicalResidual
import ExactPlaneResidualPivots
namespace ExactPlaneIndexedBranch
open Module ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneRepresentativeLookup
open ExactPlaneLookupDeterminant ExactPlaneSamplerRank ExactPlaneResidualPivots
open scoped BigOperators
variable {I K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup K] [Module F K] {N : ℕ}
variable {B : Basis I F K} {priv : Fin N→K} {tag : Fin N→Plane}

noncomputable def active (B : Basis I F K) (priv : Fin N→K) (tag : Fin N→Plane)
    (x : Vec (I×Bool)) : Finset (Fin N) := by
  classical exact Finset.univ.filter (fun i=>tag i=tagChart B x (priv i))

abbrev Partial (s : Selection B priv tag) := {i : I // i∉s.full}
noncomputable def res (s : Selection B priv tag) (height : Fin N→Plane) (x : Vec (I×Bool)) (e : Fin N) :=
  height e+lift s height x (priv e)

theorem row_iff (x : Vec (I×Bool)) (e : Fin N) :
    ExactPlanePinnedSampling.Matched (fun e side=>test B (priv e) side)
      (fun e side=>component side (tag e)) x e ↔ tag e=tagChart B x (priv e) := by
  constructor
  · intro h
    exact Prod.ext (by simpa [test_apply,component] using (h false).symm)
      (by simpa [test_apply,component] using (h true).symm)
  · intro h side
    simpa only [test_apply] using congrArg (component side) h.symm

theorem code_ind (s : Selection B priv tag) (height : Fin N→Plane) (e f : Fin N) (x : Vec (I×Bool)) :
    ExactPlaneDeterminant.independent (code s height e false).read (code s height f false).read
      (code s height e true).read (code s height f true).read x ↔ Independent (res s height x e) (res s height x f) := by
  simp only [ExactPlaneDeterminant.independent,Independent,code_read,component,res,
    LinearMap.fst_apply,LinearMap.snd_apply,Prod.mk.eta]

theorem anchor_iff (s : Selection B priv tag) (x : Vec (I×Bool)) :
    s.Eligible x ↔ ∀ t : Partial s,tag (s.anchor t.val t.property)=tagChart B x (priv (s.anchor t.val t.property)) := by
  constructor
  · intro ok t
    simpa [s.anchor_key,tagChart] using ok t.val t.property
  · intro h i hi
    simpa [s.anchor_key,tagChart] using h ⟨i,hi⟩

theorem final_support (s : Selection B priv tag) (height : Fin N→Plane) (y : Vec (I×Bool))
    (ok : s.Eligible y) (e f : Fin N) (he : e∈active B priv tag y) (hf : f∈active B priv tag y)
    (ind : Independent (res s height y e) (res s height y f)) :
    ∃ (U : Fin 2→Finset (Fin N)) (gains : Fin 2→Plane), LinearIndependent F gains ∧
      (∀ j,U j⊆active B priv tag y) ∧
      (∀ j,∑ i∈U j,ExactPlanePhysicalResidual.col priv tag height i=(0,0,gains j)) ∧ U 0≠U 1 := by
  classical
  let idx := fun i=>s.rep i (target y i)
  let p := fun j : Fin 2=>if j=0 then res s height y e else res s height y f
  have mem (i) (hi : i∈active B priv tag y) :
      res s height y i∈ExactPlanePhysicalResidual.indexedSpan (active B priv tag y)
        (ExactPlanePhysicalResidual.residual priv height (lift s height y)) := Submodule.subset_span ⟨i,hi,rfl⟩
  have hits (j : Fin 2) : p j∈ExactPlanePhysicalResidual.indexedSpan (active B priv tag y)
        (ExactPlanePhysicalResidual.residual priv height (lift s height y)) := by
    dsimp [p]; split <;> first | exact mem e he | exact mem f hf
  obtain ⟨U,sub,real,ne⟩ := ExactPlanePhysicalResidual.independent_supports
    (active B priv tag y) priv tag height (tagChart B y) (lift s height y)
    (fun i hi=>(Finset.mem_filter.mp hi).2) B idx
    (fun j =>Finset.mem_filter.mpr ⟨Finset.mem_univ _,(rep_maps s height ok j).2.1⟩)
    (fun j=>(rep_maps s height ok j).1)
    (fun j=>by simpa only [(rep_maps s height ok j).1] using (rep_maps s height ok j).2.2) p ind hits
  exact ⟨U,p,ind,sub,real,ne⟩
end ExactPlaneIndexedBranch
