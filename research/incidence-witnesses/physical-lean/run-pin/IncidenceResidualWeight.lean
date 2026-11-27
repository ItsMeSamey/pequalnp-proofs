import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace IncidenceResidualWeight
open scoped BigOperators

/-- Nonempty producer components carry at most one unit of singleton weight.
Empty producers may carry up to k, but consume a copy of their exit weight. -/
theorem ledger {ι : Type*} (nonempty empty : Finset ι) (excess weight : ι → ℕ)
    (n s k bad good : ℕ)
    (locals : good+bad=n)
    (live : n+((∑ i ∈ nonempty, excess i)+(∑ i ∈ empty, excess i))=s+1)
    (owners : nonempty.card≤n) (paid : bad≤∑ i ∈ nonempty, excess i)
    (thin : ∀ i∈nonempty, weight i≤1) (cap : ∀ i∈empty, weight i≤k)
    (demand : k*good+(∑ i ∈ empty, weight i) ≤
      (∑ i ∈ nonempty, (excess i+1)*weight i) +
      (∑ i ∈ empty, (excess i+1)*weight i)) :
    2*n-1-(2*n)/(k+1) ≤ s := by
  have small : (∑ i ∈ nonempty, (excess i+1)*weight i) ≤
      (∑ i ∈ nonempty, excess i)+nonempty.card := by
    calc
      _ ≤ ∑ i ∈ nonempty, (excess i+1)*1 :=
        Finset.sum_le_sum (fun i hi => Nat.mul_le_mul_left _ (thin i hi))
      _ = _ := by simp [Finset.sum_add_distrib]
  have large : (∑ i ∈ empty, (excess i+1)*weight i) ≤
      (∑ i ∈ empty, excess i)*k+(∑ i ∈ empty, weight i) := by
    simp only [Nat.add_mul,one_mul,Finset.sum_add_distrib,Finset.sum_mul]
    exact Nat.add_le_add_right (Finset.sum_le_sum (fun i hi =>
      Nat.mul_le_mul_left _ (cap i hi))) _
  let a := ∑ i ∈ nonempty, excess i
  let b := ∑ i ∈ empty, excess i
  have base : k*good ≤ a+n+b*k := by dsimp [a,b]; omega
  have mulPaid := Nat.mul_le_mul_left k paid
  change k*bad ≤ k*a at mulPaid
  change n+(a+b)=s+1 at live
  have kn : k*n ≤ n+(k+1)*(a+b) := by
    rw [← locals,Nat.mul_add]
    nlinarith [base,mulPaid]
  by_cases enough : 2*n ≤ s+1
  · exact (Nat.sub_le _ _).trans (by omega : 2*n-1 ≤ s)
  let delta := 2*n-(s+1)
  have eq : delta+(s+1)=2*n := by dsimp [delta]; omega
  have times := congrArg (fun j : Nat => (k+1)*j) eq
  have timesLive := congrArg (fun j : Nat => (k+1)*j) live
  have fit : delta*(k+1) ≤ 2*n := by nlinarith [times,timesLive]
  have div := (Nat.le_div_iff_mul_le (by omega : 0 < k+1)).2 fit
  change 2*n-(s+1) ≤ 2*n/(k+1) at div
  clear * - div
  omega

example : 2*215071-1-(2*215071)/(135+1)=426979 := by decide
#print axioms ledger
end IncidenceResidualWeight
