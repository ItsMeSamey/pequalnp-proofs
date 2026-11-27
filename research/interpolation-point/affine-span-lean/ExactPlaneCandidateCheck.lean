import ExactPlanePhysicalConverse
import ExactPlanePhysicalResidual

namespace ExactPlaneCandidateCheck
open ExactPlanePhysicalConverse
open scoped BigOperators
variable {I K B H : Type*} [DecidableEq I]
variable [AddCommGroup K] [AddCommGroup B] [AddCommGroup H]
variable [DecidableEq K] [DecidableEq B] [DecidableEq H]

def total (k : I → K) (b : I → B) (h : I → H) (U : Finset I) : K × B × H :=
  ∑ i ∈ U, (k i,b i,h i)

/-- Each entry carries its physical support, even when several supports have equal sums. -/
def evidence (A : Finset I) (k : I → K) (b : I → B) (h : I → H) :
    Finset (Finset I × (B × H)) :=
  ((A.powerset.filter (fun U => (total k b h U).1=0))).image
    (fun U => (U,(total k b h U).2))

def traceValues (A : Finset I) (k : I → K) (b : I → B) (h : I → H) : Finset (B × H) :=
  (evidence A k b h).image Prod.snd

def required [Fintype H] : Finset (B × H) :=
  Finset.univ.image (fun y : H => ((0:B),y))

def check [Fintype H] (A : Finset I) (k : I → K) (b : I → B) (h : I → H) : Bool :=
  decide (traceValues A k b h = required)

theorem mem_evidence (A : Finset I) (k : I → K) (b : I → B) (h : I → H)
    (U : Finset I) (z : B) (y : H) :
    (U,z,y) ∈ evidence A k b h ↔ U⊆A ∧ total k b h U=(0,z,y) := by
  constructor
  · intro mem
    obtain ⟨S,hs,eq⟩ := Finset.mem_image.mp mem
    have su : S=U := congrArg Prod.fst eq
    subst S
    have both := Finset.mem_filter.mp hs
    have second : (total k b h U).2 = (z,y) := congrArg (fun t : Finset I × (B × H) => t.2) eq
    exact ⟨Finset.mem_powerset.mp both.1,Prod.ext both.2 second⟩
  · rintro ⟨sub,eq⟩
    exact Finset.mem_image.mpr ⟨U,Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr sub,congrArg Prod.fst eq⟩,by simp [eq]⟩

theorem mem_values (A : Finset I) (k : I → K) (b : I → B) (h : I → H)
    (z : B) (y : H) :
    (z,y)∈traceValues A k b h ↔ ∃ U : Finset I, U⊆A ∧ total k b h U=(0,z,y) := by
  constructor
  · intro mem
    obtain ⟨⟨U,t⟩,hU,ht⟩ := Finset.mem_image.mp mem
    change t=(z,y) at ht
    subst t
    exact ⟨U,(mem_evidence _ _ _ _ _ _ _).mp hU⟩
  · rintro ⟨U,hU⟩
    exact Finset.mem_image.mpr ⟨(U,z,y),(mem_evidence _ _ _ _ _ _ _).mpr hU,rfl⟩

theorem mem_required [Fintype H] (z : B) (y : H) :
    (z,y)∈(required : Finset (B × H)) ↔ z=0 := by
  constructor
  · intro hit
    obtain ⟨v,_,eq⟩ := Finset.mem_image.mp hit
    exact (congrArg Prod.fst eq).symm
  · rintro rfl
    exact Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩

variable [Module F K] [Module F B] [Module F H]

theorem values_iff_span (A : Finset I) (k : I → K) (b : I → B) (h : I → H)
    (z : B) (y : H) :
    (z,y)∈traceValues A k b h ↔ (0,z,y)∈physicalSpan k b h A := by
  rw [mem_values]
  have family : Set.range (fun i : ↥A => (k i.val,b i.val,h i.val)) =
      (fun i : I => (k i,b i,h i)) '' (A : Set I) := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  unfold physicalSpan
  rw [family]
  exact (ExactPlanePhysicalResidual.physical_support A
    (fun i => (k i,b i,h i)) ((0:K),z,y)).symm

theorem check_iff [Fintype H] (A : Finset I) (k : I → K) (b : I → B) (h : I → H) :
    check A k b h=true ↔ ExactTrace k b h A := by
  simp only [check,decide_eq_true_eq]
  constructor
  · intro eq z y
    rw [← values_iff_span,eq,mem_required]
  · intro ok
    ext ⟨z,y⟩
    rw [values_iff_span,mem_required]
    exact ok z y

#print axioms mem_evidence
#print axioms check_iff
end ExactPlaneCandidateCheck
