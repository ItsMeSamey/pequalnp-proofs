import ExactPlanePhysicalConverse
import Mathlib.LinearAlgebra.Quotient.Basic
namespace ExactPlaneForcedLine
open ExactPlanePhysicalConverse
variable {I K B : Type*} [DecidableEq I] [AddCommGroup K] [Module F K] [AddCommGroup B] [Module F B]
abbrev V (K B : Type*) := K × B × F
def col (k : I→K) (b : I→B) (h : I→F) (i : I) : V K B := (k i,b i,h i)
private theorem span_image (k : I→K) (b : I→B) (h : I→F) (A : Finset I) :
    physicalSpan k b h A=Submodule.span F ((col k b h) '' (A:Set I)) := by
  unfold physicalSpan
  congr 1
  ext x
  exact ⟨fun ⟨i,e⟩ => ⟨i.val,i.property,e⟩,fun ⟨i,hi,e⟩ => ⟨⟨i,hi⟩,e⟩⟩

abbrev Q (k : I→K) (b : I→B) (h : I→F) (C : Finset I) :=
  V K B ⧸ physicalSpan k b h C

def qcol (k : I→K) (b : I→B) (h : I→F) (C : Finset I) (i : I) : Q k b h C :=
  (physicalSpan k b h C).mkQ (col k b h i)

def named (k : I→K) (b : I→B) (h : I→F) (C : Finset I) (v : B×F) : Q k b h C :=
  (physicalSpan k b h C).mkQ (0,v)

def QTrace (k : I→K) (b : I→B) (h : I→F) (C R : Finset I) : Prop :=
  ∀ z : B,∀ y : F,named k b h C (z,y)∈Submodule.span F (qcol k b h C '' (R:Set I)) ↔ z=0

theorem union_iff (k : I→K) (b : I→B) (h : I→F) (C R : Finset I) :
    ExactTrace k b h (C∪R) ↔ QTrace k b h C R := by
  let S := physicalSpan k b h C
  let T := physicalSpan k b h R
  have img : Submodule.span F (qcol k b h C '' (R:Set I))=T.map S.mkQ := by
    rw [show T=Submodule.span F (col k b h '' (R:Set I)) from span_image _ _ _ _,Submodule.map_span,
      Set.image_image]
    rfl
  have un : physicalSpan k b h (C∪R)=T⊔S := by
    rw [span_image,Finset.coe_union,Set.image_union,Submodule.span_union,sup_comm]
    rw [←span_image,←span_image]
  have eq (v : B×F) : named k b h C v∈Submodule.span F (qcol k b h C '' (R:Set I)) ↔
      ((0:K),v)∈physicalSpan k b h (C∪R) := by
    rw [img,un]
    change ((0:K),v)∈(T.map S.mkQ).comap S.mkQ ↔ _
    rw [Submodule.comap_map_eq,Submodule.ker_mkQ]
  exact ⟨fun h z y=>(eq (z,y)).trans (h z y),fun h z y=>(eq (z,y)).symm.trans (h z y)⟩

theorem forced_iff (k : I→K) (b : I→B) (h : I→F) (C : Finset I) :
    (∃ A,C⊆A ∧ ExactTrace k b h A) ↔ ∃ R,Disjoint R C ∧ QTrace k b h C R := by
  constructor
  · rintro ⟨A,inc,ok⟩
    exact ⟨A \ C,Finset.sdiff_disjoint,(union_iff k b h C _).mp (by
      rwa [Finset.union_sdiff_of_subset inc])⟩
  · rintro ⟨R,_,ok⟩
    exact ⟨C∪R,Finset.subset_union_left,(union_iff k b h C R).mpr ok⟩

def Compatible (k : I→K) (b : I→B) (h : I→F) (C : Finset I) : Prop :=
  ∀ z y,((0:K),z,y)∈physicalSpan k b h C → z=0

theorem axis_yes (k : I→K) (b : I→B) (h : I→F) (C : Finset I)
    (ok : Compatible k b h C) (axis : ((0:K),(0:B),(1:F))∈physicalSpan k b h C) :
    ExactTrace k b h C := by
  intro z y
  refine ⟨ok z y,?_⟩
  rintro rfl
  simpa using (physicalSpan k b h C).smul_mem y axis

theorem named_injective (k : I→K) (b : I→B) (h : I→F) (C : Finset I)
    (ok : Compatible k b h C) (axis : ((0:K),(0:B),(1:F))∉physicalSpan k b h C) :
    Function.Injective (named k b h C) := by
  rintro ⟨z,y⟩ ⟨z',y'⟩ eq
  have diff := (Submodule.Quotient.eq (physicalSpan k b h C)).mp eq
  change ((0:K)-0,z-z',y-y')∈physicalSpan k b h C at diff
  rw [sub_zero] at diff
  have same := ok _ _ diff
  rw [same] at diff
  have bit : ∀ a : F,a=0 ∨ a=1 := by decide
  have he : y-y'=0 := (bit _).resolve_right (fun e => axis (e ▸ diff))
  exact Prod.ext (sub_eq_zero.mp same) (sub_eq_zero.mp he)

theorem compatible_of_chart (k : I→K) (b : I→B) (h : I→F) (C : Finset I)
    (g : K→ₗ[F] B) (matched : ∀ i∈C,g (k i)=b i) : Compatible k b h C := by
  let T : V K B →ₗ[F] B := (LinearMap.fst F B F).comp (LinearMap.snd F K (B×F))
    - g.comp (LinearMap.fst F K (B×F))
  have le : physicalSpan k b h C ≤ LinearMap.ker T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change b i.val - g (k i.val)=0
    rw [matched _ i.property,sub_self]
  intro z y mem
  have eq := le mem
  change z-g 0=0 at eq
  simpa using eq

theorem named_independent {J : Type*} (k : I→K) (b : I→B) (h : I→F) (C : Finset I)
    (ok : Compatible k b h C) (axis : ((0:K),(0:B),(1:F))∉physicalSpan k b h C)
    (v : J→B×F) (li : LinearIndependent F v) :
    LinearIndependent F (fun j => named k b h C (v j)) := by
  let L : B×F →ₗ[F] Q k b h C := (physicalSpan k b h C).mkQ.comp (LinearMap.inr F K (B×F))
  have inj : Function.Injective L := named_injective k b h C ok axis
  exact li.map' L (LinearMap.ker_eq_bot.mpr inj)

#print axioms named_independent
#print axioms forced_iff
#print axioms axis_yes
#print axioms named_injective
end ExactPlaneForcedLine
