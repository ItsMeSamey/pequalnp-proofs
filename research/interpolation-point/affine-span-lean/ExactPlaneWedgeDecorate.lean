import ExactPlaneWedgePlanPhysical
import ExactPlaneIntersectionCoordinates
import ExactPlaneIntersectionDense
import Mathlib.Data.List.Nodup
namespace ExactPlaneWedgeDecorate
open Submodule Module ExactPlaneWedgeTree ExactPlaneWedgePlan ExactPlaneWedgePlanPhysical
open ExactPlaneWedgeCodec ExactPlaneWedgeProduct ExactPlanePhysicalWedgeTree
open ExactPlaneIntersectionBasis (basisRows basisRows_spec)
variable {d n : ℕ}
def subspace (k : Fin n → Word d) (s : Finset (Fin n)) :=
  span F (k '' (s : Set (Fin n)))

def cutFor (k : Fin n → Word d) (sites ext : Finset (Fin n)) : Cut d :=
  let xs := ExactPlaneIntersectionDense.basisRows k (sites.sort (·≤·)) (ext.sort (·≤·))
  ⟨xs.length,xs.get⟩

theorem represent_rows (xs : List (Word d)) (D : Submodule F (Word d))
    (nd : xs.Nodup) (ind : LinearIndepOn F id (ExactPlaneFeatureStream.sites xs))
    (sp : span F (ExactPlaneFeatureStream.sites xs)=D) :
    Represents (⟨xs.length,xs.get⟩ : Cut d) D := by
  obtain ⟨e,he⟩ := ExactPlaneIntersectionBasis.list_coordinates xs D nd ind sp
  refine ⟨e,fun x=>?_⟩
  rw [he]
  funext j
  simp [image,Finset.sum_apply,smul_eq_mul]

theorem cutFor_spec (k : Fin n→Word d) (s ext : Finset (Fin n)) :
    Represents (cutFor k s ext) (subspace k s ⊓ subspace k ext) := by
  unfold cutFor
  rw [ExactPlaneIntersectionDense.basisRows_eq]
  let xs := basisRows k (s.sort (·≤·)) (ext.sort (·≤·))
  obtain ⟨nd,li,sp,_⟩ := basisRows_spec k (s.sort (·≤·)) (ext.sort (·≤·))
  apply represent_rows xs _ nd li
  simpa [ExactPlaneIntersectionBasis.space,subspace] using sp

def decorate (k : Fin n→Word d) : Tree n→Finset (Fin n)→Indexed d n
  | .leaf i,s => .leaf i (cutFor k {i} s)
  | .join l r,s => .join (decorate k l (leaves r ∪ s)) (decorate k r (leaves l ∪ s))
      (cutFor k (leaves l ∪ leaves r) s)

theorem tree_decorate (k : Fin n→Word d) (t : Tree n) (s : Finset (Fin n)) :
    tree (decorate k t s)=t := by
  induction t generalizing s with
  | leaf => rfl
  | join l r il ir => simp only [decorate,tree,il,ir]

theorem decorate_valid (k : Fin n→Word d) (t : Tree n) (s : Finset (Fin n)) :
    Valid k (decorate k t s) (subspace k s) := by
  have union (a b : Finset (Fin n)) : subspace k (a∪b)=subspace k a⊔subspace k b := by
    simp [subspace,Set.image_union,Submodule.span_union]
  have same (a : Tree n) : keySpan k a = subspace k (leaves a) := keySpan_eq k a
  induction t generalizing s with
  | leaf i =>
    simpa only [decorate,Valid,boundary,tree,same,leaves] using cutFor_spec k {i} s
  | join l r il ir =>
    simp only [decorate,Valid,boundary,tree,tree_decorate,same,leaves]
    exact ⟨cutFor_spec k _ _,union _ _ ▸ il (leaves r ∪ s),union _ _ ▸ ir (leaves l ∪ s)⟩

#print axioms decorate_valid
end ExactPlaneWedgeDecorate
