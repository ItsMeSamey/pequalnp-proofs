import ThresholdSharedOrBudget
import ThresholdGraphCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
namespace ThresholdSharedPartition
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdRegularSource ThresholdSimpleIncidence
open ThresholdOrExtraction ThresholdSharedOrBudget
open scoped BigOperators
variable {C : Circuit} {n : Nat} (L : Layout C n)
def hubs (C : Circuit) (n : Nat) := (sharedOrs C n).toFinset
noncomputable def hits (w : Fin n) := endpoints L w ∩ hubs C n
noncomputable def missed := Finset.univ.filter (fun w : Fin n => hits L w=∅)
noncomputable def internal := Finset.univ.filter (fun w : Fin n => 2≤(hits L w).card)
noncomputable def singleAt (u : T2OrPartition.Id C) :=
  Finset.univ.filter (fun w : Fin n => hits L w={u})

theorem partition :
    n=(missed L).card+(internal L).card+∑ u∈hubs C n, (singleAt L u).card := by
  classical
  let H := hubs C n
  have point (w : Fin n) :
      1=(if hits L w=∅ then 1 else 0)+(if 2≤(hits L w).card then 1 else 0)+
        ∑ u∈H, (if hits L w={u} then 1 else 0 : Nat) := by
    by_cases h : (hits L w).card=1
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h
      have mem : v∈H := Finset.mem_of_mem_inter_right (show v∈hits L w by simp [hv])
      simp [hv,mem]
    · have none (u : T2OrPartition.Id C) : hits L w≠{u} := fun e => h (by simp [e])
      simp only [none,ite_false,Finset.sum_const_zero,Nat.add_zero]
      by_cases e : hits L w=∅
      · simp [e]
      · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr e)
        have hi : 2≤(hits L w).card := by omega
        simp [hi,e]
  have total := Finset.sum_congr (s₁:=Finset.univ) rfl (fun w _ => point w)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_comm (s:=Finset.univ) (t:=H)] at total
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
    Finset.sum_boole,Nat.cast_id,missed,internal,singleAt,H] using total
#print axioms partition
end ThresholdSharedPartition
