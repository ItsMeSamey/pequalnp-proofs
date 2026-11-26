import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

namespace ExactPlaneSubsetPolynomial

variable {ι R : Type*} [AddCommMonoid R]

/-- The input is the support of a Boolean assignment. A squarefree monomial
indexed by S is present exactly when S is contained in that support. -/
def eval (c : Finset ι → R) (A : Finset ι) : R :=
  ∑ S ∈ A.powerset, c S

/-- Each coefficient indexed by more than d variables vanishes. -/
def degreeLE (d : ℕ) (c : Finset ι → R) : Prop :=
  ∀ S, d < S.card → c S = 0

/-- Testing the Boolean ball of radius d determines whether every coefficient
through degree d vanishes, even when the polynomial has higher terms. -/
theorem low_coeff_zero_iff_low_eval_zero (c : Finset ι → R) (d : ℕ) :
    (∀ S : Finset ι, S.card ≤ d → c S = 0) ↔
      ∀ A : Finset ι, A.card ≤ d → eval c A = 0 := by
  classical
  constructor
  · intro coeff A small
    apply Finset.sum_eq_zero
    intro S mem
    exact coeff S ((Finset.card_le_card (Finset.mem_powerset.mp mem)).trans small)
  · intro tests
    have recover (n : ℕ) : ∀ S : Finset ι, S.card = n → n ≤ d → c S = 0 := by
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro S card small
        have top : eval c S = c S := by
          unfold eval
          apply Finset.sum_eq_single S
          · intro T mem ne
            have strict : T ⊂ S :=
              Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp mem, ne⟩
            have lt : T.card < n := by simpa only [card] using Finset.card_lt_card strict
            exact ih T.card lt T rfl (lt.le.trans small)
          · intro absent
            exact False.elim (absent (Finset.mem_powerset.mpr (fun _ h => h)))
        exact top.symm.trans (tests S (by simpa only [card] using small))
    exact fun S small => recover S.card S rfl small

theorem coeff_zero_iff_low_eval_zero {c : Finset ι → R} {d : ℕ} (degree : degreeLE d c) :
    (∀ S, c S = 0) ↔ ∀ A : Finset ι, A.card ≤ d → eval c A = 0 := by
  constructor
  · intro coeff
    exact (low_coeff_zero_iff_low_eval_zero c d).mp (fun S _ => coeff S)
  · intro tests S
    by_cases small : S.card ≤ d
    · exact (low_coeff_zero_iff_low_eval_zero c d).mpr tests S small
    · exact degree S (Nat.lt_of_not_ge small)

theorem eval_zero_of_low_eval_zero {c : Finset ι → R} {d : ℕ} (degree : degreeLE d c)
    (tests : ∀ A : Finset ι, A.card ≤ d → eval c A = 0) (A : Finset ι) : eval c A = 0 := by
  have coeff := (coeff_zero_iff_low_eval_zero degree).mpr tests
  exact (low_coeff_zero_iff_low_eval_zero c A.card).mp (fun S _ => coeff S) A le_rfl

theorem exists_small_nonzero {c : Finset ι → R} {d : ℕ} (degree : degreeLE d c)
    (nonzero : ∃ A : Finset ι, eval c A ≠ 0) :
    ∃ S : Finset ι, S.card ≤ d ∧ eval c S ≠ 0 := by
  classical
  by_contra! none
  obtain ⟨A,hA⟩ := nonzero
  exact hA (eval_zero_of_low_eval_zero degree none A)

#print axioms low_coeff_zero_iff_low_eval_zero
#print axioms exists_small_nonzero
end ExactPlaneSubsetPolynomial
