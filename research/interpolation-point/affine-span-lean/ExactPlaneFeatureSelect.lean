import ExactPlaneFeatureStream
import ExactPlaneWedgeLayout

namespace ExactPlaneFeatureStream
open ExactPlaneWedgeProduct (Feature)
open ExactPlaneWedgeLayout (dim store flatten flatten_injective)
open Submodule
variable {n : ℕ} {P : Type*}

def selectPayloads (f : P→Feature n) (xs : List P) : List P := select (fun p => store n (f p)) xs

theorem selectPayloads_spec (f : P→Feature n) (xs : List P) :
    let ys := selectPayloads f xs
    ys.Sublist xs ∧ ys.Nodup ∧ LinearIndepOn F f (sites ys) ∧
      span F (f '' sites ys)=span F (f '' sites xs) ∧ ys.length≤1+2*n+n.choose 2 := by
  let v := fun p => store n (f p)
  have packed : features v=(flatten n) ∘ f := by
    funext p i
    exact ExactPlaneWedgeLayout.store_get n (f p) i
  obtain ⟨sub,nd,ind,eq,bd⟩ := select_spec v xs
  rw [packed] at ind eq
  refine ⟨sub,nd,LinearIndependent.of_comp (flatten n) ind,?_,?_⟩
  · apply Submodule.map_injective_of_injective (flatten_injective n)
    rw [Submodule.map_span,Submodule.map_span,←Set.image_comp,←Set.image_comp]
    exact eq
  · change (select v xs).length≤1+2*n+n.choose 2
    exact bd.trans_eq (ExactPlaneWedgeLayout.dim_eq n)

def selectFeatures (xs : List (Feature n)) : List (Feature n) := selectPayloads id xs

theorem selectFeatures_spec (xs : List (Feature n)) :
    let ys := selectFeatures xs
    ys.Sublist xs ∧ ys.Nodup ∧ LinearIndepOn F id (sites ys) ∧
      span F (sites ys)=span F (sites xs) ∧ ys.length≤1+2*n+n.choose 2 := by
  simpa only [selectFeatures,Set.image_id] using selectPayloads_spec id xs

#print axioms selectPayloads_spec
#print axioms selectFeatures_spec
end ExactPlaneFeatureStream
