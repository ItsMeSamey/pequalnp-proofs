import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Prod
namespace ExactPlanePhysicalConverse
open scoped BigOperators
abbrev F := ZMod 2
variable {I K B H : Type*} [AddCommGroup K] [Module F K]
  [AddCommGroup B] [Module F B] [AddCommGroup H] [Module F H]

def physicalSpan (k : I→K) (b : I→B) (h : I→H) (A : Finset I) :
    Submodule F (K × (B × H)) :=
  Submodule.span F (Set.range (fun i : ↥A => (k i.val,b i.val,h i.val)))

def ExactTrace (k : I→K) (b : I→B) (h : I→H) (A : Finset I) : Prop :=
  ∀ z : B,∀ y : H,((0:K),z,y)∈physicalSpan k b h A ↔ z=0

/-- An explicit subspace equality for the intersection with the marked space
gives exactly the pointwise trace predicate. -/
theorem trace_of_intersection (k : I→K) (b : I→B) (h : I→H) (A : Finset I)
    (intersection : physicalSpan k b h A ⊓ LinearMap.ker (LinearMap.fst F K (B×H)) =
      LinearMap.ker ((LinearMap.fst F K (B×H)).prod
        ((LinearMap.fst F B H).comp (LinearMap.snd F K (B×H))))) :
    ExactTrace k b h A := by
  intro z y
  let v : K×(B×H) := (0,z,y)
  have eq := congrArg (fun P : Submodule F (K×(B×H)) => v∈P) intersection
  have both := eq.to_iff
  change ((v∈physicalSpan k b h A ∧ (0:K)=0) ↔ ((0:K),z)=0) at both
  simpa [v] using both

theorem factor {X : Type*} [AddCommGroup X] [Module F X]
    (p : X →ₗ[F] K) (tag : X →ₗ[F] B) (compat : LinearMap.ker p≤LinearMap.ker tag) :
    ∃ g : K →ₗ[F] B, g.comp p=tag := by
  let quot := (LinearMap.ker p).liftQ tag compat
  let localTag := quot.comp p.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g,ext⟩ := LinearMap.exists_extend localTag
  refine ⟨g,?_⟩
  apply LinearMap.ext
  intro x
  have agree := LinearMap.congr_fun ext (⟨p x,⟨x,rfl⟩⟩ : LinearMap.range p)
  change g (p x)=quot (p.quotKerEquivRange.symm ⟨p x,_⟩) at agree
  have inverse := p.quotKerEquivRange_symm_apply_image x (LinearMap.mem_range_self p x)
  exact agree.trans (congrArg quot inverse)

theorem chart (k : I→K) (b : I→B) (h : I→H) (A : Finset I) (trace : ExactTrace k b h A) :
    ∃ g : K →ₗ[F] B,∀ i∈A,g (k i)=b i := by
  let X := physicalSpan k b h A
  let p : X →ₗ[F] K := (LinearMap.fst F K (B×H)).comp X.subtype
  let tag : X →ₗ[F] B := ((LinearMap.fst F B H).comp (LinearMap.snd F K (B×H))).comp X.subtype
  have compat : LinearMap.ker p≤LinearMap.ker tag := by
    rintro ⟨⟨u,z,y⟩,hx⟩ zero
    change u=0 at zero
    subst u
    exact (trace z y).mp hx
  obtain ⟨g,cal⟩ := factor p tag compat
  refine ⟨g,?_⟩
  intro i hi
  have mem : (k i,b i,h i)∈X := Submodule.subset_span ⟨(⟨i,hi⟩ : ↥A),rfl⟩
  exact LinearMap.congr_fun cal ⟨_,mem⟩

theorem gain_relations (k : I→K) (b : I→B) (h : I→H) (A : Finset I)
    (trace : ExactTrace k b h A) (y : H) :
    ∃ c : ↥A→F, (∑ i : ↥A,c i • k i.val)=0 ∧
      (∑ i : ↥A,c i • b i.val)=0 ∧ (∑ i : ↥A,c i • h i.val)=y := by
  classical
  have mem := (trace 0 y).mpr rfl
  obtain ⟨c,eq⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp mem
  refine ⟨c,?_,?_,?_⟩
  · simpa [Prod.fst_sum] using congrArg Prod.fst eq
  · simpa [Prod.fst_sum,Prod.snd_sum] using congrArg (fun x : K×(B×H) => x.2.1) eq
  · simpa [Prod.snd_sum] using congrArg (fun x : K×(B×H) => x.2.2) eq

theorem forget_tag (k : I→K) (b : I→B) (h : I→H) (A : Finset I) (trace : ExactTrace k b h A)
    (y : H) : ((0:K),y)∈Submodule.span F (Set.range (fun i : ↥A => (k i.val,h i.val))) := by
  classical
  obtain ⟨c,kz,_,hy⟩ := gain_relations k b h A trace y
  apply (Submodule.mem_span_range_iff_exists_fun F).mpr
  refine ⟨c,Prod.ext ?_ ?_⟩
  · simpa [Prod.fst_sum] using kz
  · simpa [Prod.snd_sum] using hy

theorem active_relations (k : I→K) (b : I→B) (h : I→H) (A : Finset I) (trace : ExactTrace k b h A) :
    ∃ g : K →ₗ[F] B,(∀ i∈A,g (k i)=b i) ∧
    ∀ (L : K →ₗ[F] H) (y : H),∃ c : ↥A→F,(∑ i : ↥A,c i • k i.val)=0 ∧
       (∑ i : ↥A,c i • b i.val)=0 ∧ (∑ i : ↥A,c i • (h i.val+L (k i.val)))=y := by
  classical
  obtain ⟨g,ok⟩ := chart k b h A trace
  refine ⟨g,ok,?_⟩
  intro L y
  obtain ⟨c,kz,bz,hv⟩ := gain_relations k b h A trace y
  refine ⟨c,kz,bz,?_⟩
  have lc := congrArg L kz
  simp only [map_sum,map_smul,map_zero] at lc
  simp only [smul_add,Finset.sum_add_distrib,hv,lc,add_zero]

#print axioms active_relations
end ExactPlanePhysicalConverse
