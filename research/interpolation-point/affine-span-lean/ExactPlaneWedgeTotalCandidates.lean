import ExactPlaneWedgeArrayCharges
import ExactPlaneWedgeTreeCharges
import Batteries.Tactic.OpenPrivate
namespace ExactPlaneWedgeTotalCandidates
open ExactPlaneWedgeArrayDP ExactPlaneWedgeTreeCharges
open private atOf from ExactPlaneWedgeArrayDP
variable {n : Nat}
def candidates (compress : Rows n→Rows n) : {m : Nat}→Plan n m→Nat
  | m,.leaf _ rows => ((List.finRange m).map (fun i=>(rows i).length)).sum
  | m,.join left right _ ok =>
    let a := run compress left
    let b := run compress right
    candidates compress left+candidates compress right+
      ((List.finRange m).map (fun i=>(joined (ok i) a b).length)).sum

def leafCap (s : Nat) : {m : Nat}→Plan n m→Prop
  | _,.leaf _ rows => ∀ i,(rows i).length≤s
  | _,.join a b _ _ => leafCap s a ∧ leafCap s b

theorem cell_cap (compress : Rows n→Rows n) (D : Nat) (cap : ∀xs,(compress xs).length≤D)
    {m : Nat} (p : Plan n m) (i : Fin m) : ((run compress p)[i]).length≤D := by
  cases p <;> simpa [run,atOf] using cap _

private theorem sumBound (I : Type*) (l : List I) (f : I→Nat) (K : Nat) (h : ∀i,f i≤K) :
    (l.map f).sum≤l.length*K := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    simpa only [Nat.add_comm K (l.length*K)] using Nat.add_le_add (h i) ih

theorem total_cap (compress : Rows n→Rows n) (D Q s : Nat) (cap : ∀xs,(compress xs).length≤D)
    {m : Nat} (p : Plan n m) (fit : Fits Q p) (leafOK : leafCap s p) :
    candidates compress p ≤ tips p*(Q*s)+checks p*(D*D) := by
  induction p with
  | leaf m rows =>
    have bd := sumBound _ (List.finRange m) (fun i=>(rows i).length) s leafOK
    simpa [candidates,tips,checks] using (bd.trans (Nat.mul_le_mul_right s (by simpa [Fits] using fit)))
  | @join a b l r m ok hl hr =>
    have one (i : Fin m) := ExactPlaneWedgeArrayCharges.actual_cap (ok i) (run compress l) (run compress r) D
      (cell_cap compress D cap l) (cell_cap compress D cap r)
    have bd := sumBound _ (List.finRange m) (fun i=>(joined (ok i) (run compress l) (run compress r)).length)
      (a*(b*(D*D))) one
    simp only [List.length_finRange] at bd
    simpa [candidates,tips,checks,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using Nat.add_le_add (Nat.add_le_add (hl fit.1 leafOK.1) (hr fit.2.1 leafOK.2)) bd
#print axioms total_cap
end ExactPlaneWedgeTotalCandidates
