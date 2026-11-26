import ExactPlaneFrozenBranch
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace ExactPlaneIndexedBranch
open Module ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneRepresentativeLookup
open ExactPlaneResidualPivots
open ExactPlanePhysicalConverse (ExactTrace physicalSpan)
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup K] [Module F K] {N : ℕ}
variable {B : Basis I F K} {priv : Fin N→K} {tag : Fin N→Plane}

/-- Soundness checks only the actual sites and their original tags and heights. -/
theorem success_trace (s : Selection B priv tag) (height : Fin N→Plane) (y : Vec (I×Bool))
    (hs : Success s height y) : ExactTrace priv tag height (active B priv tag y) := by
  classical
  obtain ⟨_,U,gains,ind,inside,realized,_⟩ := hs
  let A := active B priv tag y
  let S := physicalSpan priv tag height A
  let g := tagChart B y
  let diff : (K × (Plane × Plane)) →ₗ[F] Plane :=
    (LinearMap.fst F Plane Plane).comp (LinearMap.snd F K (Plane × Plane)) -
      g.comp (LinearMap.fst F K (Plane × Plane))
  have agree : S ≤ LinearMap.ker diff := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change tag i.val - g (priv i.val) = 0
    exact sub_eq_zero.mpr (Finset.mem_filter.mp i.property).2
  let vert : Plane →ₗ[F] K × (Plane × Plane) :=
    (0 : Plane →ₗ[F] K).prod ((0 : Plane →ₗ[F] Plane).prod LinearMap.id)
  have lower : Submodule.span F (Set.range gains) ≤ S.comap vert := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change ((0:K),(0:Plane),gains j) ∈ S
    rw [← realized j]
    exact S.sum_mem fun i hi => Submodule.subset_span ⟨⟨i,inside j hi⟩,rfl⟩
  have whole := ind.span_eq_top_of_card_eq_finrank
    (by simp [Plane,Module.finrank_prod] : Fintype.card (Fin 2) = finrank F Plane)
  rw [whole] at lower
  intro z h
  constructor
  · intro hz
    have eq := agree hz
    change z - g 0 = 0 at eq
    simpa using eq
  · rintro rfl
    exact lower (show h ∈ (⊤ : Submodule F Plane) from trivial)

#print axioms success_trace
end ExactPlaneIndexedBranch
