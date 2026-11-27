import ExactPlaneFeatureStream
import Batteries.Tactic.OpenPrivate
namespace ExactPlaneWedgePivotCharges
open ExactPlaneFeatureStream
open private back back_spec from ExactPlaneFeatureStream
variable {D : Nat} {P : Type*}

def bankAfter (v : P→Vector F D) (xs : List P) :=
  (xs.foldl (step v) ([],[])).1

theorem bank_bound (v : P→Vector F D) (xs : List P) : (bankAfter v xs).length≤D := by
  have mirror : bankAfter v xs=(back v xs.reverse).1 := by
    simp [bankAfter,back,List.foldr_reverse,Function.flip_def]
  rw [mirror]
  obtain ⟨_,_,_,_,_,ech,_⟩ := back_spec v xs.reverse
  simpa [ExactPlaneGaussianMaterialized.readBank] using ExactPlaneGaussian.bank_length_le ech

-- Each suffix step visits exactly one cell of the elimination bank for each pivot in it.
def visits (v : P→Vector F D) (past : List P) : List P→Nat
  | [] => 0
  | x::xs => (bankAfter v past).length + visits v (past++[x]) xs

theorem visit_cap (v : P→Vector F D) (past xs : List P) :
    visits v past xs≤xs.length*D := by
  induction xs generalizing past with
  | nil => simp [visits]
  | cons x xs ih =>
    simp only [visits,List.length_cons,Nat.succ_mul]
    simpa only [Nat.add_comm D (xs.length*D)] using Nat.add_le_add (bank_bound v past) (ih (past++[x]))

#print axioms visit_cap
end ExactPlaneWedgePivotCharges
