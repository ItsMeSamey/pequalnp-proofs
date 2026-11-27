import ExactPlaneAffineSubstitution
import Mathlib.Data.Finset.Lattice.Fold
namespace ExactPlaneSparseANF
open ExactPlaneAffineSubstitution ExactPlaneSubsetPolynomial
open scoped BigOperators
abbrev Form (I : Type*) := Finset (Finset I)
variable {I : Type*} [DecidableEq I]
def coeff (s : Form I) : Coeff I := fun A => if A∈s then 1 else 0
def plus (s t : Form I) : Form I := (s\t) ∪ (t\s)
theorem coeff_plus (s t : Form I) (A : Finset I) :
    coeff (plus s t) A=coeff s A+coeff t A := by
  by_cases hs : A∈s <;> by_cases ht : A∈t <;> simp [coeff,plus,hs,ht] <;> decide

def normalize (xs : List (List I)) : Form I :=
  xs.foldr (fun raw s => plus {raw.toFinset} s) ∅
theorem coeff_normalize (xs : List (List I)) (A : Finset I) :
    coeff (normalize xs) A=(xs.map fun raw => if A=raw.toFinset then (1:F) else 0).sum := by
  induction xs with
  | nil => simp [normalize,coeff]
  | cons x l ih =>
    change coeff (plus {x.toFinset} (normalize l)) A=_
    rw [coeff_plus,ih]
    simp [coeff]

def unions (s t : Form I) : Form I := (s ×ˢ t).image (fun p => p.1∪p.2)
def fiber (s t : Form I) (A : Finset I) : F :=
  ∑ S∈s, ∑ T∈t, if S∪T=A then 1 else 0
def times (s t : Form I) : Form I :=
  (unions s t).filter (fun A => fiber s t A ≠ 0)

private theorem fiber_zero {s t : Form I} {A : Finset I} (miss : A∉unions s t) :
    fiber s t A=0 := by
  apply Finset.sum_eq_zero; intro S hS
  apply Finset.sum_eq_zero; intro T hT
  exact if_neg (fun eq => miss (Finset.mem_image.mpr ⟨(S,T),Finset.mem_product.mpr ⟨hS,hT⟩,eq⟩))
theorem coeff_times [Fintype I] (s t : Form I) (A : Finset I) :
    coeff (times s t) A=product (coeff s) (coeff t) A := by
  have toFiber : coeff (times s t) A = fiber s t A := by
    by_cases hit : A∈unions s t
    · have bit : ∀ z:F,z=0 ∨ z=1 := by decide
      rcases bit (fiber s t A) with h|h <;> simp [coeff,times,hit,h]
    · simp [coeff,times,hit,fiber_zero hit]
  rw [toFiber,product]
  change (∑ S∈s, ∑ T∈t, if S∪T=A then (1:F) else 0)=_
  have cut (S : Finset I) (hS : S∈s) :
      (∑ T∈t, if S∪T=A then (1:F) else 0) =
      ∑ T : Finset I, if S∪T=A then coeff s S*coeff t T else 0 := by
    classical
    calc
      _ = ∑ T∈t, if S∪T=A then coeff s S*coeff t T else 0 := by
        apply Finset.sum_congr rfl; intro T hT; simp [coeff,hS,hT]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (by intro T _ hT; simp [coeff,hT])
  calc
    _ = ∑ S∈s,∑ T : Finset I, if S∪T=A then coeff s S*coeff t T else 0 :=
      Finset.sum_congr rfl cut
    _ = _ := Finset.sum_subset (Finset.subset_univ _) (by intro S _ hS; simp [coeff,hS])

def degree (s : Form I) : ℕ := s.sup Finset.card
theorem degree_iff (s : Form I) (D : ℕ) :
    degree s ≤ D ↔ degreeLE D (coeff s) := by
  rw [degree,Finset.sup_le_iff]
  constructor
  · intro cap A big
    exact if_neg (fun h => (Nat.not_lt_of_ge (cap A h)) big)
  · intro cap A h
    by_contra! big
    simpa [coeff,h] using cap A big
#print axioms coeff_times
end ExactPlaneSparseANF
