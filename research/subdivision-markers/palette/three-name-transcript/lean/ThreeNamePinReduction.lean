import ExactPlaneGaussian
import Mathlib.LinearAlgebra.Quotient.Basic

namespace ThreeNamePinReduction
open ExactPlaneGaussian
variable {I B : Type*} [DecidableEq I] {d : ℕ}
variable [AddCommGroup B] [Module F B]

/-- Replay each stored Gaussian pivot as a linear map on value coordinates. -/
def normal : Bank d I → V d →ₗ[F] V d
  | [] => LinearMap.id
  | (i,p)::s => (normal s).comp (LinearMap.id + (LinearMap.proj i).smulRight p.1)

theorem residual (bank : Bank d I) (row : Row d I) :
    (reduce bank row).1 = normal bank row.1 := by
  induction bank generalizing row with
  | nil => rfl
  | cons a s ih => exact ih (clear a.1 a.2 row)

def project (col : I → V d) (pins : List I) := normal (build col pins)

def indexedSpan (col : I → V d) (ids : Finset I) :=
  Submodule.span F (col '' (ids : Set I))

theorem killed_iff (col : I → V d) (pins : List I) (x : V d) :
    project col pins x = 0 ↔ x ∈ indexedSpan col pins.toFinset := by
  change _ ↔ x ∈ Submodule.span F (col '' (pins.toFinset : Set I))
  rw [← solve_hits pins col x]
  unfold solve project
  simp only [residual]
  by_cases h : normal (build col pins) x = 0 <;> simp [h]

theorem coeffs_of_killed [Fintype I] (col : I → V d) (pins : List I) (x : V d)
    (hx : project col pins x = 0) :
    ∃ mask, solve pins col x = some mask ∧ decode col mask = x ∧ ∀ i ∉ pins, mask i = 0 := by
  obtain ⟨m,hm⟩ := (solve_hits pins col x).mpr ((killed_iff _ _ _).mp hx)
  exact ⟨m,hm,solve_witness pins col x m hm⟩

theorem kernel (col : I → V d) (pins : List I) :
    LinearMap.ker (project col pins) = indexedSpan col pins.toFinset := by
  ext x
  exact killed_iff _ _ _

theorem union_membership (col : I → V d) (pins : List I) (R : Finset I) (x : V d) :
    project col pins x ∈ indexedSpan (fun i => project col pins (col i)) R ↔
      x ∈ indexedSpan col (pins.toFinset ∪ R) := by
  let q := project col pins
  have img : indexedSpan (fun i => q (col i)) R = (indexedSpan col R).map q := by
    rw [indexedSpan, indexedSpan, Submodule.map_span, Set.image_image]
  have un : indexedSpan col (pins.toFinset ∪ R) =
      indexedSpan col R ⊔ indexedSpan col pins.toFinset := by
    rw [indexedSpan, indexedSpan, indexedSpan, Finset.coe_union, Set.image_union, Submodule.span_union, sup_comm]
  change q x ∈ indexedSpan (fun i => q (col i)) R ↔ _
  rw [img, un]
  change x ∈ ((indexedSpan col R).map q).comap q ↔ _
  rw [Submodule.comap_map_eq, kernel]

def Exact (col : I → V d) (name : (B × F) →ₗ[F] V d) (A : Finset I) :=
  ∀ z y, name (z,y) ∈ indexedSpan col A ↔ z = 0

def Compatible (col : I → V d) (name : (B × F) →ₗ[F] V d) (pins : List I) :=
  ∀ z y, name (z,y) ∈ indexedSpan col pins.toFinset → z = 0

theorem lift_iff (col : I → V d) (name : (B × F) →ₗ[F] V d) (pins : List I) (R : Finset I) :
    Exact (fun i => project col pins (col i)) ((project col pins).comp name) R ↔
      Exact col name (pins.toFinset ∪ R) := by
  constructor <;> intro h z y
  · exact (union_membership col pins R _).symm.trans (h z y)
  · exact (union_membership col pins R _).trans (h z y)

theorem lift_original_ids (col : I → V d) (name : (B × F) →ₗ[F] V d) (pins : List I) (R : Finset I)
    (h : Exact (fun i => project col pins (col i)) ((project col pins).comp name) R) :
    pins.toFinset ⊆ pins.toFinset ∪ R ∧ Exact col name (pins.toFinset ∪ R) :=
  ⟨Finset.subset_union_left, (lift_iff col name pins R).mp h⟩

theorem pinned_exists (col : I → V d) (name : (B × F) →ₗ[F] V d) (pins : List I) :
    (∃ A, pins.toFinset ⊆ A ∧ Exact col name A) ↔
    ∃ R, Disjoint R pins.toFinset ∧ Exact (fun i => project col pins (col i)) ((project col pins).comp name) R := by
  constructor
  · rintro ⟨A,hA,h⟩
    exact ⟨A \ pins.toFinset,Finset.sdiff_disjoint,(lift_iff _ _ _ _).mpr (by
      rwa [Finset.union_sdiff_of_subset hA])⟩
  · rintro ⟨R,_,h⟩
    exact ⟨_,lift_original_ids col name pins R h⟩

theorem incompatible_no (col : I → V d) (name : (B × F) →ₗ[F] V d) (pins : List I)
    (bad : ¬ Compatible col name pins) :
    ¬ ∃ A, pins.toFinset ⊆ A ∧ Exact col name A := by
  rintro ⟨A,inc,h⟩
  apply bad
  intro z y hz
  exact (h z y).mp (Submodule.span_mono (Set.image_mono inc) hz)

theorem axis_yes (col : I → V d) (name : (B × F) →ₗ[F] V d) (pins : List I)
    (ok : Compatible col name pins) (axis : project col pins (name (0,1)) = 0) :
    Exact col name pins.toFinset := by
  intro z y
  refine ⟨ok z y, ?_⟩
  rintro rfl
  have h : y • ((0:B),(1:F)) = (0,y) := by ext <;> simp
  rw [← h, map_smul]
  exact (indexedSpan col pins.toFinset).smul_mem y ((killed_iff _ _ _).mp axis)

theorem named_injective (col : I → V d) (name : (B × F) →ₗ[F] V d) (pins : List I)
    (ok : Compatible col name pins) (axis : project col pins (name (0,1)) ≠ 0) :
    Function.Injective ((project col pins).comp name) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  rintro ⟨z,y⟩ killed
  change project col pins (name (z,y)) = 0 at killed
  have z0 := ok z y ((killed_iff _ _ _).mp killed)
  subst z
  have bits : ∀ a:F, a=0 ∨ a=1 := by decide
  rcases bits y with eq | eq
  · simp [eq]
  · exact (axis (eq ▸ killed)).elim

#print axioms coeffs_of_killed
#print axioms pinned_exists
#print axioms incompatible_no
#print axioms axis_yes
#print axioms named_injective
end ThreeNamePinReduction
