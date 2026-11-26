import ThresholdReceiverCounts
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdOrGroups
open ThresholdFanoutBudget ThresholdSharedPartition ThresholdSharedFlow T2SoleOrSplice
namespace ThresholdPrivateOwners
variable {C : Circuit} {n : Nat} (L : Layout C n)
def privateRoots (C : Circuit) (n : Nat) := Finset.univ.filter (fun i : Id C =>
  next C n i=none ∧ T2OrPartition.isOr C i=true ∧ i∉hubs C n)
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


include L in
theorem private_budget (M : LexMinimum n C) :
    (privateRoots C n).card≤2*(andIds C).length+1 := by
  classical
  let S := privateRoots C n
  let num : Id C ↪ Nat := ⟨fun i => n+i.val,fun i j eq => Fin.ext (Nat.add_left_cancel eq)⟩
  let A := (andPins C).toFinset
  have sub : S.map num⊆A∪{C.output} := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨_,st,org,priv⟩ := Finset.mem_filter.mp hi
    rcases stopped_class L M i st org with hub|pin|out
    · exact False.elim (priv hub)
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr pin)
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr out)
  have cap := Finset.card_le_card sub
  have un := Finset.card_union_le A {C.output}
  have pin : A.card≤2*(andIds C).length := (List.toFinset_card_le _).trans_eq (and_pin_count L)
  simp only [Finset.card_map,Finset.card_singleton] at cap un
  change S.card≤_
  omega

theorem purity_ledger {h l p a d r hi s : ℤ}
    (groups : p≤2*a+1) (gap : d=s+1-h)
    (slots : r=s+h+p-a) (outgoing : hi+2*(h-l)≤r+2*a) :
    hi≤d+3*a+2*l := by omega

theorem gap_ledger {h p d B : ℤ} (h0 : 0≤h)
    (cap : h*(d+3-p)≤B) : h*d≤B+h*(p-3) := by
  simp only [mul_sub,mul_add] at cap ⊢
  omega

#print axioms private_budget
end ThresholdPrivateOwners
