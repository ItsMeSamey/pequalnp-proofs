import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Sort
import ExactPlaneIntersectionDense
import ExactPlaneIntersectionCoordinates
import ExactPlanePhysicalWedgeTree
namespace ExactPlanePhysicalIntersection
open ExactPlaneWedgeTree
open ExactPlaneWedgeProduct (V F)
open ExactPlanePhysicalWedgeTree ExactPlaneIntersectionBasis
open scoped BigOperators
variable {n d : Nat}

def rows (k : Fin n→V d) (A B : Finset (Fin n)) :=
  ExactPlaneIntersectionDense.basisRows k (A.sort (·≤·)) (B.sort (·≤·))

theorem coordinates (k : Fin n→V d) (A B : Finset (Fin n)) :
    let xs := rows k A B
    ∃ e : V xs.length ≃ₗ[F] ↥(Submodule.span F (k '' (A:Set (Fin n))) ⊓
      Submodule.span F (k '' (B:Set (Fin n)))), ∀ x,(e x : V d)=∑ i,x i • xs.get i := by
  dsimp only
  unfold rows
  rw [ExactPlaneIntersectionDense.basisRows_eq]
  have h := ExactPlaneIntersectionBasis.coordinates k (A.sort (·≤·)) (B.sort (·≤·))
  dsimp only at h
  have keySpace (S : Finset (Fin n)) :
      space k (S.sort (·≤·)) = Submodule.span F (k '' (S:Set (Fin n))) := by
    unfold space
    rw [Finset.sort_toFinset]
  rw [keySpace A,keySpace B] at h
  exact h

theorem tree_coordinates (k : Fin n→V d) (t : Tree n) (exterior : Finset (Fin n)) :
    let xs := rows k (leaves t) exterior
    ∃ e : V xs.length ≃ₗ[F] ↥(keySpan k t ⊓ Submodule.span F (k '' (exterior:Set (Fin n)))),
      ∀ x,(e x : V d)=∑ i,x i • xs.get i := by
  rw [keySpan_eq]
  exact coordinates _ _ _

theorem rows_length (k : Fin n→V d) (A B : Finset (Fin n)) :
    (rows k A B).length=Module.finrank F
      ↥(Submodule.span F (k '' (A:Set (Fin n))) ⊓ Submodule.span F (k '' (B:Set (Fin n)))) := by
  obtain ⟨e,_⟩ := coordinates k A B
  simpa [ExactPlaneWedgeProduct.V] using e.finrank_eq

#print axioms rows_length
#print axioms tree_coordinates
end ExactPlanePhysicalIntersection
