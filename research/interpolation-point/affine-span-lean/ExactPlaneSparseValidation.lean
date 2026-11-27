import ExactPlaneSparseSections
namespace ExactPlaneSparseValidation
open ExactPlaneSparseANF ExactPlaneSparseSections ExactPlaneAffineSubstitution ExactPlaneSubsetPolynomial
open scoped BigOperators
variable {I : Type*} [DecidableEq I] [Fintype I] {N r d : ℕ}

def constant (c : F) : Form I := if c=0 then ∅ else {∅}
theorem eval_constant (c : F) (A : Finset I) : eval (coeff (constant c)) A=c := by
  have bit : ∀ x:F,x=0 ∨ x=1 := by decide
  rcases bit c with rfl|rfl <;> simp [eval,coeff,constant]
theorem eval_empty (A : Finset I) : eval (coeff (∅ : Form I)) A=0 := by simp [eval,coeff]

/-- A bit of bad i is 1 exactly when the corresponding physical tag constraint fails. -/
def check (f : Fin r→Fin N→Form I) (bad : Fin N→Bool→Form I)
    (k : Fin N→Fin d→F) (u : Fin r→Fin d→F) : Bool :=
  decide (∀ j i side, times (f j i) (bad i side)=∅) &&
    decide (∀ j c,lc (f j) (fun i=>k i c)=constant (u j c))

theorem sound {f : Fin r→Fin N→Form I} {bad : Fin N→Bool→Form I}
    {k : Fin N→Fin d→F} {u : Fin r→Fin d→F} (ok : check f bad k u=true)
    (j : Fin r) (A : Finset I) :
    (∀ i∈chosen (f j) A, ∀ side,eval (coeff (bad i side)) A=0) ∧
    (∑ i∈chosen (f j) A,k i)=u j := by
  obtain ⟨support,key⟩ := (show (∀ j i side,times (f j i) (bad i side)=∅) ∧
      ∀ j c,lc (f j) (fun i=>k i c)=constant (u j c) from by simpa [check] using ok)
  constructor
  · intro i hi side
    have hot := (Finset.mem_filter.mp hi).2
    have e : eval (product (coeff (f j i)) (coeff (bad i side))) A=0 := by
      have ident : product (coeff (f j i)) (coeff (bad i side))=
          coeff (times (f j i) (bad i side)) := funext fun U=>(coeff_times _ _ U).symm
      rw [ident,support,eval_empty]
    rwa [product_eval,hot,one_mul] at e
  · funext c
    simpa only [Finset.sum_apply,key,eval_constant] using chosen_sum (f j) (fun i=>k i c) A

#print axioms sound
end ExactPlaneSparseValidation
