import ThresholdReceiverPortUse
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdOrGroups
open ThresholdFanoutBudget ThresholdSharedPartition ThresholdSharedFlow T2SoleOrSplice
namespace ThresholdSecondaryReceivers
variable {C : Circuit} {n : Nat} (L : Layout C n)
private theorem owner_or (i : Id C) (org : T2OrPartition.isOr C i=true) :
    T2OrPartition.isOr C (owner C n i)=true := by
  cases e : next C n i with
  | none => simpa [owner_of_stop C n i e] using org
  | some j => rw [owner_of_next C n i j e]; exact owner_or j.val (next_is_or e).2
termination_by C.gates.length-i.val
decreasing_by have hj := j.val.isLt; have lt := j.property; change i.val<j.val.val at lt; omega

include L in
private theorem stopped_class (M : LexMinimum n C) (i : Id C) (s : next C n i=none)
    (org : T2OrPartition.isOr C i=true) :
    i∈hubs C n ∨ n+i.val∈andPins C ∨ n+i.val=C.output := by
  by_cases obs : n+i.val=C.output
  · exact Or.inr (Or.inr obs)
  by_cases shared : 2≤(readers C (n+i.val)).length
  · exact Or.inl (by simp [hubs,ThresholdSharedOrBudget.sharedOrs,ThresholdSharedOrBudget.sharedGates,org,shared])
  have live := live_slots L M i (Ne.symm obs)
  obtain ⟨q,one⟩ : ∃ q, readers C (n+i.val)=[q] := by
    cases h : readers C (n+i.val) with
    | nil => simp [h] at live
    | cons q rs => cases rs with
      | nil => exact ⟨q,rfl⟩
      | cons _ _ => simp [h] at shared
  have pin := reader_pin (C:=C) (w:=n+i.val) (j:=q) (by simp [one])
  have lt : i < q := by
    have l := (L.atIndex q).leftEarlier
    have r := (L.atIndex q).rightEarlier
    rw [layout_inputs (L.atIndex q)] at pin
    simp only [List.mem_cons,List.not_mem_nil,or_false] at pin
    change i.val < q.val
    rcases pin with h|h <;> omega
  have non := singleton_target s org (Ne.symm obs) one lt
  exact Or.inr (Or.inl (List.mem_flatMap.mpr ⟨q,by simp [andIds,non],pin⟩))

theorem receiver_budget (M : LexMinimum n C) (H : Finset (Id C))
    (anti : ∀ u∈H, ∀ v∈H, u≠v → active L u v=false) :
    (receivers C n H).card ≤ ((hubs C n) \ H).card+2*(andIds C).length+1 := by
  classical
  let S := receivers C n H
  let num : Id C ↪ Nat := ⟨fun i => n+i.val,fun i j eq => Fin.ext (Nat.add_left_cancel eq)⟩
  let privatePins := (andPins C).toFinset
  have sub : S.map num ⊆ (((hubs C n) \ H).map num ∪ privatePins) ∪ {C.output} := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨u,hu,hit⟩ := Finset.mem_biUnion.mp hi
    have spec := Finset.mem_filter.mp hu
    have down := receiver_later L hu hit
    have outside : i∉H := fun h => by have := anti u spec.1 i h down.1.ne; simp [down.2] at this
    obtain ⟨q,hq,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hit)
    have org := owner_or (n:=n) q (spec.2.2 q hq)
    have stop := (owner_spec C n q).2
    rw [eq] at org stop
    rcases stopped_class L M i stop org with hh|ha|out
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨i,Finset.mem_sdiff.mpr ⟨hh,outside⟩,rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr ha))
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr out)
  have h := Finset.card_le_card sub
  have outer := Finset.card_union_le ((((hubs C n) \ H).map num) ∪ privatePins) {C.output}
  have inner := Finset.card_union_le (((hubs C n) \ H).map num) privatePins
  have pin := (List.toFinset_card_le (andPins C)).trans_eq (and_pin_count L)
  simp only [Finset.card_map,Finset.card_singleton] at h outer inner
  change S.card ≤ _
  change privatePins.card ≤ _ at pin
  omega
end ThresholdSecondaryReceivers
