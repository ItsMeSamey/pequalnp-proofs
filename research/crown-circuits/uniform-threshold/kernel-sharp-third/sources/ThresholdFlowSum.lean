import ThresholdFlowPairs
import ThresholdFlowFanout
namespace ThresholdFlowSum
open PEqualNP.CircuitLowerBounds ThresholdSimpleIncidence ThresholdOrExtraction T2OrPartition
open ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowPairs ResidualSurplus
variable {C : Circuit} {n : Nat} (L : Layout C n)

def deltaO := ∑ i∈hubs C n, (fan L i-2)
def deltaA := ∑ i : Id C, if L.op i=.and then fan L i-1 else 0

private theorem hub_iff (i : Id C) :
    i∈hubs C n ↔ 2≤fan L i ∧ L.op i=.or := by
  simp [hubs,ThresholdSharedOrBudget.sharedOrs,ThresholdSharedOrBudget.sharedGates,
    fan_readers,ThresholdOrExtraction.physical_op L,and_comm]

theorem row_upper (U : Id C) (member : U∈hubs C n) :
    (∑ i : Id C, budget L U i) ≤ fan L U +
    (∑ i∈hubs C n, if U≠i ∧ active L U i=true then 1 else 0) +
    (∑ i∈(hubs C n).erase U, (fan L i-2)) + deltaA L := by
  let H := hubs C n
  let hot := fun i : Id C => if U≠i ∧ active L U i=true then 1 else 0
  have point (i : Id C) : budget L U i ≤
      (if i=U then fan L U else 0) + (if i∈H then hot i else 0) +
      (if i∈H.erase U then fan L i-2 else 0) +
      (if L.op i=.and then fan L i-1 else 0) := by
    by_cases e : i=U
    · subst i; cases a : active L U U <;> simp [budget,a,hot]
    · by_cases mem : i∈H
      · have geo := (hub_iff L i).mp mem
        cases a : active L U i <;> simp [budget,e,Ne.symm e,mem,geo.2,hot,a] <;> omega
      · have bad : ¬(2≤fan L i ∧ L.op i=.or) := fun h => mem ((hub_iff L i).mpr h)
        cases a : active L U i <;> cases op : L.op i <;> simp [budget,e,mem,a,op] <;> simp_all <;> omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => point i)
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_ite_mem,Finset.univ_inter,deltaA,hot,H] using sum

theorem boundary (per : ∀ u∈hubs C n, (singleAt L u).card ≤ 1+max (fan L u) (leak L u)) :
    (∑ u∈hubs C n, (singleAt L u).card) ≤ 3*(hubs C n).card+deltaO L+
      (hotPairs L).card+((hubs C n).card-1)*deltaO L+(hubs C n).card*deltaA L := by
  let H := hubs C n
  let hot := fun (u i : Id C) => if u≠i ∧ active L u i=true then 1 else 0
  have point (u : Id C) (hu : u∈H) : (singleAt L u).card ≤
      (1+fan L u)+(∑ i∈H,hot u i)+(∑ i∈H.erase u,(fan L i-2))+deltaA L := by
    have p := (probe_flow L u).trans (row_upper L u hu)
    have q := per u hu
    dsimp [H,hot] at *
    omega
  have hotTotal : (∑ u∈H, ∑ i∈H, hot u i)=(hotPairs L).card := by
    rw [hotPairs,Finset.card_filter,Finset.sum_product]
  have base : (∑ u∈H, (1+fan L u))=3*H.card+deltaO L := by
    have p (u : Id C) (hu : u∈H) : 1+fan L u=3+(fan L u-2) := by
      have := ((hub_iff L u).mp hu).1; omega
    rw [Finset.sum_congr rfl p,Finset.sum_add_distrib]
    simp [deltaO,H,Nat.mul_comm]
  have extra : (∑ u∈H, ∑ i∈H.erase u, (fan L i-2))=(H.card-1)*deltaO L := by
    have t (u : Id C) : (∑ i∈H.erase u, (fan L i-2)) =
        ∑ i∈H, if i≠u then fan L i-2 else 0 := by rw [←Finset.sum_filter]; congr 1; ext; simp [and_comm]
    simp_rw [t]
    change _ = (H.card-1)*(∑ i∈H, (fan L i-2))
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←Finset.sum_filter]
    have eq : H.filter (fun u => i≠u)=H.erase i := by ext u; simp [ne_comm,and_comm]
    simp [eq,Finset.card_erase_of_mem hi]
  have total := Finset.sum_le_sum point
  simpa only [Finset.sum_add_distrib,base,hotTotal,extra,Finset.sum_const,smul_eq_mul,H] using total
end ThresholdFlowSum
