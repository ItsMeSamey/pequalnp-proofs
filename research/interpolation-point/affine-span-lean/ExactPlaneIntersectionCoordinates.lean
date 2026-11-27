import ExactPlaneIntersectionBasis
import Mathlib.LinearAlgebra.Basis.Basic
namespace ExactPlaneIntersectionBasis
open ExactPlaneGaussian Submodule Module
open ExactPlaneFeatureStream (sites)
open scoped BigOperators

theorem list_coordinates {d : ℕ} (xs : List (V d)) (J : Submodule F (V d))
    (nd : xs.Nodup) (ind : LinearIndepOn F id (sites xs)) (eq : span F (sites xs)=J) :
    ∃ e : V xs.length ≃ₗ[F] J, ∀ x, (e x : V d) = ∑ i,x i • xs.get i := by
  classical
  let row : Fin xs.length → ↥(sites xs) := fun i=>⟨xs.get i,List.get_mem ..⟩
  have ri : Function.Injective row := fun i j h => (List.nodup_iff_injective_get.mp nd)
    (congrArg Subtype.val h)
  have li : LinearIndependent F xs.get := ind.comp row ri
  have ran : Set.range xs.get=sites xs := by
    ext z
    exact List.mem_iff_get.symm
  have eq' : span F (Set.range xs.get)=J := (congrArg (span F) ran).trans eq
  let b := Basis.span li
  let e := b.equivFun.symm.trans (LinearEquiv.ofEq _ _ eq')
  refine ⟨e,fun x=>?_⟩
  change ((b.equivFun.symm x : span F (Set.range xs.get)) : V d)=_
  rw [Basis.equivFun_symm_apply]
  simp [b]

theorem coordinates {d n : Nat} (v : Fin n→V d) (l r : List (Fin n)) :
    let rows := basisRows v l r
    ∃ e : V rows.length ≃ₗ[F] ↥(space v l ⊓ space v r),
      ∀ x, (e x : V d)=∑ i,x i • rows.get i := by
  obtain ⟨nd,li,eq,_⟩ := basisRows_spec v l r
  exact list_coordinates _ _ nd li eq

#print axioms coordinates
end ExactPlaneIntersectionBasis
