import ThresholdSharedPartition
import Mathlib.Algebra.BigOperators.Fin
namespace ThresholdSharedFunding
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdSharedPartition T2OrPartition
open T2SoleOrSplice T2CubeDeletion ResidualSurplus ThresholdRegularSource ThresholdFanoutBudget
open ThresholdSharedOrBudget
open scoped BigOperators
variable {C : Circuit} {n : Nat}
def fan (C : Circuit) (n : Nat) (i : Id C) := (readers C (n+i.val)).length
def extrasOr (C : Circuit) (n : Nat) := ∑ i∈hubs C n, (fan C n i-2)
def extrasAnd (L : Layout C n) := ∑ i : Id C, if L.op i=.and then fan C n i-1 else 0

theorem funding {gs : List Raw} {out : Nat} (M : LexMinimum n (source gs out))
    (reg : T2RegularOrDelete.Regular n gs) :
    let B := source gs out
    let L := layout n gs out M.eligible
    extrasOr B n + extrasAnd L + (hubs B n).card + 2*n ≤ B.size+1 := by
  classical
  intro B L
  let H := hubs B n
  let f := fan B n
  let obs := fun i : Id B => B.output=n+i.val
  have mem (i : Id B) : i∈H ↔ 2≤f i ∧ isOr B i=true := by
    simp [H,hubs,sharedOrs,sharedGates,f,fan,and_comm]
  have point (i : Id B) :
      (if i∈H then f i-2 else 0)+(if L.op i=.and then f i-1 else 0)+
        (if i∈H then 1 else 0)+1 ≤ f i+(if obs i then 1 else 0) := by
    have live : ¬obs i → 1≤f i := fun no => live_slots L M i no
    by_cases hi : i∈H
    · have op := (physical_op L i).mp ((mem i).mp hi).2
      have f2 := ((mem i).mp hi).1
      simp [hi,op]; omega
    · simp only [hi,ite_false,Nat.zero_add,Nat.add_zero]
      by_cases o : obs i <;> by_cases a : L.op i=.and <;> simp [o,a] <;> omega
  have summed := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => point i)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at summed
  have monoObs : (∑ i : Id B, if obs i then 1 else 0 : Nat) ≤ 1 := by
    by_cases any : ∃ j,obs j
    · obtain ⟨j,hj⟩ := any
      have uniq (i : Id B) : obs i ↔ i=j := by
        change B.output=n+i.val ↔ i=j
        change B.output=n+j.val at hj
        constructor
        · intro he; apply Fin.ext; omega
        · rintro rfl; exact hj
      simp [uniq]
    · simp [show ∀ i,¬obs i from fun i h => any ⟨i,h⟩]
  have balance : (∑ i : Id B,f i)+2*n=2*B.gates.length := by
    rw [Fin.sum_univ_def]
    exact balance_slots L (regular_inputs n gs out M.eligible reg).2.1
  dsimp only [extrasOr,extrasAnd,Circuit.size]
  dsimp only [H,f,fan,B] at summed balance monoObs ⊢
  omega
#print axioms funding
end ThresholdSharedFunding
