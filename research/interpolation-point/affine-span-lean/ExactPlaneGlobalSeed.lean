import ExactPlaneChartCoordinates
import ExactPlaneCoordinateSampler
import Mathlib.LinearAlgebra.Dimension.Free
namespace ExactPlaneGlobalSeed
open Module ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit ExactPlaneRepresentativeLookup
open ExactPlaneSamplerRank Classical
universe u v
variable {K : Type u} [AddCommGroup K] [Module F K]
variable {I : Type v} [Fintype I] [DecidableEq I]

noncomputable def equiv (D : Basis I F K) : (K →ₗ[F] F × F) ≃ₗ[F] Vec (I × Bool) where
  toFun := coordinates D
  invFun := tagChart D
  left_inv := chart_coordinates D
  right_inv x := by
    funext j
    rcases j with ⟨i,b⟩
    cases b <;> simp [coordinates,tagChart,target,component]
  map_add' g h := by
    funext j
    simp [coordinates]
  map_smul' c g := by
    funext j
    simp [coordinates]

theorem physical_seed (K : Type u) [AddCommGroup K] [Module F K] [Module.Finite F K] (R : ℕ) :
    ∃ S : Finset (K →ₗ[F] F × F), S.card ≤ max 1 ((2*(finrank F K*2)*2^R)^2) ∧
      ∀ (I : Type v) [Fintype I] [DecidableEq I] (D : Basis I F K),
        OntoHits (S.image (coordinates D)) R := by
  classical
  let B := Module.finBasis F K
  obtain ⟨S,cap,onto⟩ := ExactPlaneCoordinateSampler.all_coordinates (Fin (finrank F K) × Bool) R
  refine ⟨S.image (equiv B).symm,Finset.card_image_le.trans (by simpa using cap),?_⟩
  intro I fi de D k hk f sur y
  let E := (equiv B).symm.trans (equiv D)
  obtain ⟨s,hs,hit⟩ := onto k hk (f.comp E.toLinearMap) (sur.comp E.surjective) y
  exact ⟨coordinates D ((equiv B).symm s),
    Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨s,hs,rfl⟩,rfl⟩,hit⟩

theorem decode_list (D : Basis I F K) (S : Finset (K →ₗ[F] F × F))
    (l : List (Vec (I × Bool))) (inside : ∀ x ∈ l,x ∈ S.image (coordinates D)) :
    ∃ m : List (K →ₗ[F] F × F), (∀ g ∈ m,g ∈ S) ∧ m.length=l.length ∧
      coordinates D m.sum=l.sum ∧ tagChart D l.sum=m.sum := by
  classical
  let e := equiv D
  refine ⟨l.map e.symm,?_,by simp,?_,?_⟩
  · intro g hg
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp (inside x hx)
    change e.symm x ∈ S
    change e p = x at eq
    rw [←eq,e.symm_apply_apply]
    exact hp
  · change e (l.map e.symm).sum = l.sum
    rw [← map_list_sum e.symm l,e.apply_symm_apply]
  · change e.symm l.sum = (l.map e.symm).sum
    exact map_list_sum e.symm l

#print axioms physical_seed
#print axioms decode_list
end ExactPlaneGlobalSeed
