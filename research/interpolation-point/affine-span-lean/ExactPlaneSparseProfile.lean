import ExactPlaneSparseANF
import ExactPlaneDeterminantProfile
namespace ExactPlaneSparseProfile
open ExactPlaneSparseANF ExactPlaneAffineSubstitution ExactPlaneSubsetPolynomial
variable {I G : Type*} [DecidableEq I]
abbrev Row (I : Type*) := Form I × Form I
def row (a : Row I) : ExactPlaneDeterminantProfile.Pair I := (coeff a.1,coeff a.2)
def minor (a b : Row I) := plus (times a.1 b.2) (times b.1 a.2)
theorem minor_eq [Fintype I] (a b : Row I) : coeff (minor a b) =
    ExactPlaneDeterminantProfile.detANF (row a) (row b) := by
  funext A
  simp [minor,coeff_plus,coeff_times,ExactPlaneDeterminantProfile.detANF,row]
def actual [Fintype G] (f : G→Row I) : ℕ :=
  Finset.univ.sup (fun ij : G×G => degree (minor (f ij.1) (f ij.2)))
theorem actual_eq [Fintype I] [Fintype G] (f : G→Row I) :
    actual f = ExactPlaneDeterminantProfile.profile (fun i=>row (f i)) := by
  have cd (a : Form I) : degree a=ExactPlaneDeterminantProfile.coordDegree (coeff a) := by
    apply Nat.le_antisymm
    · exact (degree_iff _ _).mpr ((ExactPlaneDeterminantProfile.coordDegree_le _ _).mp le_rfl)
    · exact (ExactPlaneDeterminantProfile.coordDegree_le _ _).mpr ((degree_iff _ _).mp le_rfl)
  simp only [actual,ExactPlaneDeterminantProfile.profile,cd,minor_eq]

def augmented (f : G→Row I) : G⊕Bool→Row I
  | .inl i => f i
  | .inr false => ({∅},∅)
  | .inr true => (∅,{∅})

theorem row_augmented [Fintype I] (f : G→Row I) (i : G⊕Bool) :
    row (augmented f i) = ExactPlaneDeterminantProfile.augmented (fun j=>row (f j)) i := by
  cases i with
  | inl j => rfl
  | inr t =>
    cases t <;> apply Prod.ext <;> funext A <;> simp [augmented,row,coeff,
      ExactPlaneDeterminantProfile.augmented,ExactPlaneDeterminantProfile.constANF]

theorem actual_augmented_eq [Fintype I] [Fintype G] (f : G→Row I) :
    actual (augmented f) = ExactPlaneDeterminantProfile.profile
      (ExactPlaneDeterminantProfile.augmented (fun i=>row (f i))) := by
  rw [actual_eq]
  simp only [row_augmented]

#print axioms actual_augmented_eq
#print axioms actual_eq
end ExactPlaneSparseProfile
