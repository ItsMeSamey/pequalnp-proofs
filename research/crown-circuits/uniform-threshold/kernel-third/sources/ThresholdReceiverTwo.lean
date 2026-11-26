import ThresholdExternalCount
import ThresholdExternalIdempotence
import ThresholdReceiverPortUse
namespace ThresholdSecondaryReceivers
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open T2SoleOrSplice T2OrPartition ThresholdSharedPartition
theorem signature_two {C : Circuit} {n} (L : Layout C n) (inner : MeetsInternal L)
    (M : LexMinimum n C) (hn : 2≤n) (H : Finset (Id C)) (hub : H⊆hubs C n)
    (u : Id C) (hu : u∈good C n H) : (signature C n u).card=2 := by
  classical
  have spec := Finset.mem_filter.mp hu
  have shared := List.mem_toFinset.mp (hub spec.1)
  have stop := ThresholdSharedOrBudget.shared_stops (List.mem_filter.mp shared).1
  let bs := forest L Fin.val
  let w := n+u.val
  let selected := bs.filter (fun b => decide (w∈b.exts))
  have count := ThresholdExternalCount.point_count L u stop spec.2.2 Fin.val
  rw [spec.2.1] at count
  have each (b : Block) (hb : b∈bs) : b.exts.count w≤1 := by
    cases b with
    | group p t => exact ThresholdExternalIdempotence.external_once L Fin.val inner M hn p t hb w
    | meet j x y =>
      have ck := forest_checked L Fin.val _ hb
      obtain ⟨⟨pre,post,eq,idx⟩,_,_⟩ := ck
      let i : Id C := ⟨pre.length,by simp [eq]⟩
      have gate : C.gates.get i=ResidualSurplus.binary .and x y := by simp [i,eq,List.get_eq_getElem,List.getElem_append_right]
      have no : w∉[x,y] := fun hit => by
        have uses : n+u.val∈(C.gates.get i).inputs := by rw [gate]; exact hit
        have h := spec.2.2 i (read_mem uses)
        unfold T2OrPartition.isOr at h
        rw [gate] at h
        contradiction
      simp [Block.exts,List.count_eq_zero.mpr no]
  have convert (xs : List Block) (inbs : ∀ b∈xs,b∈bs) :
      (xs.filter (fun b => decide (w∈b.exts))).length=(xs.map (fun b => b.exts.count w)).sum := by
    induction xs with
    | nil => rfl
    | cons b xs ih =>
      have tail := ih (fun a ha => inbs a (by simp [ha]))
      have one := each b (inbs b (by simp))
      by_cases mem : w∈b.exts
      · have pos := List.count_pos_iff.mpr mem
        simp [List.filter_cons,mem,tail]; omega
      · simp [List.filter_cons,mem,tail,List.count_eq_zero.mpr mem]
  have total : selected.length=2 := (convert bs (fun _ h => h)).trans count
  let num : Id C ↪ Nat := ⟨fun i => n+i.val,fun i j eq => Fin.ext (Nat.add_left_cancel eq)⟩
  have subset : (selected.map Block.out).toFinset ⊆ (signature C n u).map num := by
    intro j hj
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    have hit := List.mem_filter.mp hb
    obtain ⟨i,hi,eq⟩ := receiver_use L Fin.val u b hit.1 (of_decide_eq_true hit.2)
    exact Finset.mem_map.mpr ⟨i,hi,eq.symm⟩
  have uniq := ThresholdFactorCut.output_nodup L Fin.val
  have sub : List.Sublist (selected.map Block.out) (bs.map Block.out) := (List.filter_sublist ..).map _
  have bound := Finset.card_le_card subset
  rw [List.toFinset_card_of_nodup (uniq.sublist sub),List.length_map,Finset.card_map,total] at bound
  have upper := List.toFinset_card_le (ports C n u)
  simp only [ports,List.length_map,spec.2.1] at upper
  exact Nat.le_antisymm upper bound
end ThresholdSecondaryReceivers
