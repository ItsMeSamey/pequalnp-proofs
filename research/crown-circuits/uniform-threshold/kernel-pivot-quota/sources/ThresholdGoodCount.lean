import ThresholdReceiverCounts
import ThresholdFlowSum
namespace ThresholdSecondaryReceivers
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdOrGroups
open ThresholdFanoutBudget ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowSum
variable {C : Circuit} {n : Nat} (L : Layout C n)

theorem good_count (H : Finset (Id C)) (high : H⊆hubs C n) :
    H.card ≤ (good C n H).card+deltaO L+2*(andIds C).length := by
  classical
  let wide := H.filter (fun i => 2<fan L i)
  let andRead := H.filter (fun i => n+i.val∈andPins C)
  have cap : wide.card ≤ deltaO L := by
    rw [Finset.card_eq_sum_ones]
    calc
      _ ≤ ∑ i∈wide, (fan L i-2) := by
        apply Finset.sum_le_sum
        intro i hi
        have := (Finset.mem_filter.mp hi).2
        change 2<fan L i at this
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans high)
        (fun _ _ _ => Nat.zero_le _)
  let num : Id C ↪ Nat := ⟨fun i => n+i.val,fun i j eq => Fin.ext (Nat.add_left_cancel eq)⟩
  have subPins : andRead.map num ⊆ (andPins C).toFinset := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hw
    exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
  have capAnd := (Finset.card_le_card subPins).trans ((List.toFinset_card_le _).trans_eq (and_pin_count L))
  rw [Finset.card_map] at capAnd
  have sub : H ⊆ (good C n H ∪ wide) ∪ andRead := by
    intro i hi
    have atHub := high hi
    have two : 2≤(readers C (n+i.val)).length := by
      have ss := (List.mem_filter.mp (List.mem_toFinset.mp atHub)).1
      exact of_decide_eq_true (List.mem_filter.mp ss).2
    by_cases exact2 : (readers C (n+i.val)).length=2
    · by_cases only : ∀ q∈readers C (n+i.val), T2OrPartition.isOr C q=true
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,exact2,only⟩))
      · push_neg at only
        obtain ⟨q,hq,andq⟩ := only
        have non : T2OrPartition.isOr C q=false := by simpa using andq
        have pin : n+i.val∈andPins C := List.mem_flatMap.mpr
          ⟨q,by simp [andIds,non],reader_pin hq⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,pin⟩)
    · have gt : 2<fan L i := by rw [fan_readers]; omega
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,gt⟩))
  have bound := Finset.card_le_card sub
  have outer := Finset.card_union_le (good C n H ∪ wide) andRead
  have inner := Finset.card_union_le (good C n H) wide
  omega
end ThresholdSecondaryReceivers
