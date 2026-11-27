import ExactPlanePhysicalConverse
import ExactPlanePhysicalResidual
import Mathlib.LinearAlgebra.Pi

namespace ExactPlaneFirstRelation
open ExactPlanePhysicalConverse
open scoped BigOperators
variable {I K B M : Type*} [Fintype I] [DecidableEq I]
variable [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B]
variable [AddCommGroup M] [Module F M]

def aggregate (v : I→M) : (I→F) →ₗ[F] M := ∑ i, (LinearMap.proj i).smulRight (v i)
def support (z : I→F) : Finset I := Finset.univ.filter fun i => z i=1
def mask (U : Finset I) : I→F := fun i => if i∈U then 1 else 0
def Match (g : K→ₗ[F] B) (k : I→K) (b : I→B) (U : Finset I) := ∀ i∈U,g (k i)=b i

theorem aggregate_support (v : I→M) (z : I→F) : aggregate v z=∑ i∈support z,v i := by
  rw [support,Finset.sum_filter]
  unfold aggregate
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have bit : ∀ x : F,x=0 ∨ x=1 := by decide
  rcases bit (z i) with h|h <;> simp [h]

@[simp] theorem support_mask (U : Finset I) : support (mask U)=U := by
  ext i
  by_cases h : i∈U <;> simp [support,mask,h]

def relation (k : I→K) (b : I→B) (g : K→ₗ[F] B) : Submodule F (I→F) where
  carrier := {z | aggregate k z=0 ∧ ∀ i,g (k i)≠b i → z i=0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx,ax⟩ ⟨hy,ay⟩
    exact ⟨by rw [map_add,hx,hy,add_zero],fun i hi => by simp [ax i hi,ay i hi]⟩
  smul_mem' := by
    rintro c x ⟨hx,ax⟩
    exact ⟨by rw [map_smul,hx,smul_zero],fun i hi => by simp [ax i hi]⟩

theorem mem_relation (k : I→K) (b : I→B) (g : K→ₗ[F] B) (z : I→F) :
    z∈relation k b g ↔ aggregate k z=0 ∧ Match g k b (support z) := by
  constructor
  · rintro ⟨key,away⟩
    refine ⟨key,fun i hi => ?_⟩
    by_contra miss
    have on := (Finset.mem_filter.mp hi).2
    rw [away i miss] at on
    exact zero_ne_one on
  · rintro ⟨key,matched⟩
    refine ⟨key,fun i miss => ?_⟩
    have bit : ∀ x : F,x=0 ∨ x=1 := by decide
    exact (bit _).resolve_right fun hot => miss
      (matched i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hot⟩))

noncomputable def first (k : I→K) (b : I→B) : Submodule F (I→F) := ⨆ g,relation k b g

def charge (s : I→F) : (I→F) →ₗ[F] F := aggregate s

theorem charge_rep (φ : (I→F) →ₗ[F] F) : ∃ s,charge s=φ := by
  refine ⟨fun i => φ (fun j => if i=j then 1 else 0),?_⟩
  apply LinearMap.ext
  intro z
  rw [LinearMap.pi_apply_eq_sum_univ φ z]
  simp [charge,aggregate,LinearMap.sum_apply]

theorem nonorthogonal (k : I→K) (b : I→B) (s : I→F) :
    (¬ first k b ≤ LinearMap.ker (charge s)) ↔
      ∃ g z,z∈relation k b g ∧ charge s z=1 := by
  classical
  unfold first
  rw [iSup_le_iff]
  constructor
  · intro h
    push_neg at h
    obtain ⟨g,hg⟩ := h
    obtain ⟨z,inG,out⟩ := Set.not_subset.mp hg
    have nz : charge s z≠0 := out
    have bit : ∀ x : F,x=0 ∨ x=1 := by decide
    exact ⟨g,z,inG,(bit _).resolve_left nz⟩
  · rintro ⟨g,z,inG,one⟩ safe
    have zero : charge s z=0 := safe g inG
    exact zero_ne_one (zero.symm.trans one)

theorem violating_support (k : I→K) (b : I→B) (s : I→F) :
    (¬ first k b ≤ LinearMap.ker (charge s)) ↔
      ∃ g U,Match g k b U ∧ (∑ i∈U,k i)=0 ∧ (∑ i∈U,s i)=1 := by
  rw [nonorthogonal]
  constructor
  · rintro ⟨g,z,rel,one⟩
    obtain ⟨key,ok⟩ := (mem_relation _ _ _ _).mp rel
    exact ⟨g,support z,ok,(aggregate_support k z).symm.trans key,
      (aggregate_support s z).symm.trans one⟩
  · rintro ⟨g,U,ok,key,one⟩
    refine ⟨g,mask U,(mem_relation _ _ _ _).mpr ⟨?_,by simpa using ok⟩,?_⟩
    · simpa only [aggregate_support,support_mask] using key
    · simpa only [charge,aggregate_support,support_mask] using one

private theorem span_support (k : I→K) (b : I→B) (s : I→F) (A : Finset I)
    (p : K×B×F) : p∈physicalSpan k b s A ↔
    ∃ U : Finset I,U⊆A ∧ (∑ i∈U,(k i,b i,s i))=p := by
  have fam : Set.range (fun i : ↥A => (k i.val,b i.val,s i.val)) =
      (fun i : I => (k i,b i,s i)) '' (A : Set I) := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  unfold physicalSpan
  rw [fam]
  exact ExactPlanePhysicalResidual.physical_support A _ _

/-- Recover a physical violating relation inside the supplied exact-line witness. -/
theorem extract (k : I→K) (b : I→B) (s : I→F) (A : Finset I) (ok : ExactTrace k b s A) :
    ∃ g U,U⊆A ∧ Match g k b A ∧ (∑ i∈U,k i)=0 ∧ (∑ i∈U,s i)=1 := by
  obtain ⟨g,hg⟩ := chart k b s A ok
  obtain ⟨U,sub,eq⟩ := (span_support k b s A (0,0,1)).mp ((ok 0 1).mpr rfl)
  refine ⟨g,U,sub,hg,?_,?_⟩
  · simpa only [Prod.fst_sum] using congrArg Prod.fst eq
  · simpa only [Prod.snd_sum] using congrArg (fun x : K×B×F => x.2.2) eq

theorem exact_of_support (k : I→K) (b : I→B) (s : I→F) (g : K→ₗ[F] B) (U : Finset I)
    (matched : Match g k b U) (key : (∑ i∈U,k i)=0) (one : (∑ i∈U,s i)=1) :
    ExactTrace k b s U := by
  have tag (T : Finset I) (sub : T⊆U) : (∑ i∈T,b i)=g (∑ i∈T,k i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i hi => (matched i (sub hi)).symm
  intro z y
  constructor
  · intro mem
    obtain ⟨T,sub,eq⟩ := (span_support _ _ _ _ _).mp mem
    have kz : (∑ i∈T,k i)=0 := by simpa only [Prod.fst_sum] using congrArg Prod.fst eq
    have tz : (∑ i∈T,b i)=z := by
      simpa only [Prod.fst_sum,Prod.snd_sum] using congrArg (fun p : K×B×F => p.2.1) eq
    rw [←tz,tag T sub,kz,map_zero]
  · rintro rfl
    have bit : ∀ x : F,x=0 ∨ x=1 := by decide
    rcases bit y with rfl|rfl
    · exact (physicalSpan k b s U).zero_mem
    · apply (span_support k b s U (0,0,1)).mpr
      refine ⟨U,Finset.Subset.rfl,Prod.ext ?_ (Prod.ext ?_ ?_)⟩
      · simpa only [Prod.fst_sum] using key
      · simpa only [Prod.fst_sum,Prod.snd_sum] using
          (tag U Finset.Subset.rfl).trans (by rw [key,map_zero])
      · simpa only [Prod.snd_sum] using one

theorem scalar_iff_trace (k : I→K) (b : I→B) (s : I→F) :
    (¬ first k b ≤ LinearMap.ker (charge s)) ↔ ∃ A : Finset I,ExactTrace k b s A := by
  rw [violating_support]
  constructor
  · rintro ⟨g,U,hg,key,one⟩
    exact ⟨U,exact_of_support _ _ _ g U hg key one⟩
  · rintro ⟨A,ok⟩
    obtain ⟨g,U,sub,hg,key,one⟩ := extract k b s A ok
    exact ⟨g,U,fun i hi => hg i (sub hi),key,one⟩

#print axioms scalar_iff_trace
#print axioms extract
#print axioms charge_rep
end ExactPlaneFirstRelation
