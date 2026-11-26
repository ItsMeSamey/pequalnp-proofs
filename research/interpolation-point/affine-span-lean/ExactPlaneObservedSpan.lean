import ExactPlanePhysicalConverse
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Span.Basic

namespace ExactPlaneObservedSpan
open ExactPlanePhysicalConverse Submodule Module

variable {I K B H : Type*} [AddCommGroup K] [Module F K]
  [AddCommGroup B] [Module F B] [AddCommGroup H] [Module F H]

def observed (k : I → K) : Submodule F K := span F (Set.range k)

def key (k : I → K) (i : I) : observed k :=
  ⟨k i, subset_span (Set.mem_range_self i)⟩

theorem full (k : I → K) : span F (Set.range (key k)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff (observed k)
    (fun i => (key k i).property)).2 rfl

theorem finite [Finite I] (k : I → K) : FiniteDimensional F (observed k) :=
  FiniteDimensional.span_of_finite F (Set.finite_range k)

theorem dimension_eq (k : I → K) :
    finrank F (observed k) = (Set.range k).finrank F := rfl

theorem dimension_le [Fintype I] (k : I → K) :
    finrank F (observed k) ≤ Fintype.card I := finrank_range_le_card k

private def includeKey (k : I → K) :
    (observed k × (B × H)) →ₗ[F] (K × (B × H)) :=
  (observed k).subtype.prodMap LinearMap.id

theorem map_physical (k : I → K) (b : I → B) (h : I → H) (A : Finset I) :
    (physicalSpan (key k) b h A).map (includeKey k) = physicalSpan k b h A := by
  unfold physicalSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem vertical_iff (k : I → K) (b : I → B) (h : I → H) (A : Finset I) (z : B) (y : H) :
    ((0 : observed k),z,y) ∈ physicalSpan (key k) b h A ↔
      ((0 : K),z,y) ∈ physicalSpan k b h A := by
  rw [← map_physical k b h A]
  constructor
  · intro hu
    exact ⟨(0,z,y),hu,rfl⟩
  · rintro ⟨⟨x,zh⟩,hx,he⟩
    change ((x : K),zh) = (0,(z,y)) at he
    have hzero : x = 0 := Subtype.ext (congrArg Prod.fst he)
    have hzh : zh = (z,y) := congrArg Prod.snd he
    change (x,zh) ∈ physicalSpan (key k) b h A at hx
    rw [hzero,hzh] at hx
    exact hx

theorem trace_iff (k : I → K) (b : I → B) (h : I → H) (A : Finset I) :
    ExactTrace (key k) b h A ↔ ExactTrace k b h A := by
  unfold ExactTrace
  simp only [vertical_iff]

#print axioms trace_iff
end ExactPlaneObservedSpan
