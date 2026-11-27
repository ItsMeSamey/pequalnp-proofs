import ExactPlaneSparseProfile
import Mathlib.Algebra.BigOperators.Fin
import ExactPlaneAffineSpanHit
namespace ExactPlaneSparseSections
open ExactPlaneSparseANF ExactPlaneSparseProfile ExactPlaneAffineSubstitution ExactPlaneSubsetPolynomial
open scoped BigOperators
variable {I : Type*} [DecidableEq I] {N r : Nat}
def lc (f : Fin N→Form I) (w : Fin N→F) : Form I :=
  (List.finRange N).foldr (fun j s => if w j=1 then plus (f j) s else s) ∅
theorem coeff_lc (f : Fin N→Form I) (w : Fin N→F) (U : Finset I) :
    coeff (lc f w) U = ∑ i, w i * coeff (f i) U := by
  let aux (l : List (Fin N)) := l.foldr (fun j s => if w j=1 then plus (f j) s else s) ∅
  have go (l : List (Fin N)) : coeff (aux l) U = (l.map (fun i=>w i*coeff (f i) U)).sum := by
    induction l with
    | nil => simp [aux,coeff]
    | cons i l ih =>
      have bit : ∀ x:F, x=0 ∨ x=1 := by decide
      change coeff (if w i=1 then plus (f i) (aux l) else aux l) U=_
      rcases bit (w i) with h|h <;> simp only [h,zero_ne_one,ite_false,ite_true,coeff_plus,ih,
        List.map_cons,List.sum_cons,zero_mul,one_mul,zero_add]
  simpa only [lc,aux,Fin.sum_univ_def] using go (List.finRange N)

def heights (f : Fin r→Fin N→Form I) (h : Fin N→F×F) (j : Fin r) : Row I :=
  (lc (f j) (fun i=>(h i).1),lc (f j) (fun i=>(h i).2))
theorem eval_height (f : Fin N→Form I) (w : Fin N→F) (A : Finset I) :
    eval (coeff (lc f w)) A=∑ i,w i * eval (coeff (f i)) A := by
  simp only [eval,coeff_lc,Finset.mul_sum]
  rw [Finset.sum_comm]
def chosen (f : Fin N→Form I) (A : Finset I) : Finset (Fin N) :=
  Finset.univ.filter fun i=>eval (coeff (f i)) A = 1
theorem chosen_sum (f : Fin N→Form I) (w : Fin N→F) (A : Finset I) :
    (∑ i∈chosen f A,w i)=eval (coeff (lc f w)) A := by
  rw [eval_height,chosen,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have bit : ∀ x:F,x=0 ∨ x=1 := by decide
  rcases bit (eval (coeff (f i)) A) with h|h <;> simp [h]

theorem eval_pair (f : Fin r→Fin N→Form I) (h : Fin N→F×F) (j : Fin r) (A : Finset I) :
    (∑ i∈chosen (f j) A,h i)=
    (eval (coeff (heights f h j).1) A, eval (coeff (heights f h j).2) A) := by
  apply Prod.ext
  · simpa [Prod.fst_sum,heights] using chosen_sum (f j) (fun i=>(h i).1) A
  · simpa [Prod.snd_sum,heights] using chosen_sum (f j) (fun i=>(h i).2) A

def actualD (f : Fin r→Fin N→Form I) (h : Fin N→F×F) :=
  actual (augmented (heights f h))
theorem actualD_eq [Fintype I] (f : Fin r→Fin N→Form I) (h : Fin N→F×F) :
    actualD f h=ExactPlaneDeterminantProfile.profile
      (ExactPlaneDeterminantProfile.augmented (fun j=>row (heights f h j))) :=
  actual_augmented_eq _
#print axioms eval_pair
#print axioms actualD_eq
end ExactPlaneSparseSections
