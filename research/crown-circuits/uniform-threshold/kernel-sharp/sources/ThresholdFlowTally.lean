import ThresholdFlowSum
import ThresholdSharpNatTally
namespace ThresholdFlowTally
open PEqualNP.CircuitLowerBounds ThresholdSimpleIncidence ThresholdOrExtraction T2OrPartition
open ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowPairs ThresholdFlowSum
open ThresholdSharpArithmetic ThresholdSharedOrBudget

theorem tally {C : Circuit} {n : Nat} (L : Layout C n)
    (card : ∀ e, (endpoints L e).card=2) (inj : Function.Injective (endpoints L))
    (avoid : (missed L).card≤4)
    (per : ∀ u∈hubs C n, (singleAt L u).card ≤ 1+max (fan L u) (leak L u))
    (noedge : ∀ u∈hubs C n, ∀ v∈hubs C n, u≠v → active L u v=true →
      ∀ e : Fin n, u∈endpoints L e → v∉endpoints L e)
    (fund : deltaO L+deltaA L+(hubs C n).card+2*n ≤ C.size+1) :
    Tally (n:ℤ) ((C.size:ℤ)-2*(n:ℤ)) ((sharedOrs C n).length:ℤ) := by
  have nd : (sharedOrs C n).Nodup :=
    ((List.nodup_finRange C.gates.length).filter _).filter _
  have number : (hubs C n).card=(sharedOrs C n).length :=
    List.toFinset_card_of_nodup nd
  rw [←number]
  have parts := partition L
  have pairs := pair_budget L card inj noedge
  by_cases h : 1≤(hubs C n).card
  · exact tally_of_nat_classes h (parts.trans (by omega)) avoid (boundary L per) pairs fund
  · have empty : hubs C n=∅ := Finset.card_eq_zero.mp (by omega)
    have iz : (internal L).card=0 := by simp [internal,hits,empty]
    rw [empty] at parts pairs ⊢
    simp at parts pairs ⊢
    apply tally_empty
    omega

end ThresholdFlowTally
