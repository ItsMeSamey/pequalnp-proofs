import Research.CrownIdentifyLabels
import Research.CrownIdentifyThreshold
import Research.CrownFirstSingleton

namespace PEqualNP.Research.CrownIdentify
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

def firstOnRaw (C : Circuit) (i : Fin 24) (k : Fin C.gates.length) : Prop :=
  let w := List.ofFn (fun j : Fin 24 => decide (j = i))
  (trueOrFlags C.gates w).getD k.val false = true ∧
    ∀ j < k.val, (trueOrFlags C.gates w).getD j false = false

theorem min_is_firstOnRaw (C : Circuit) (i : Fin 24)
    (pos : (activeOrIds C.gates (List.ofFn fun j : Fin 24 => decide (j = i))).Nonempty) :
    firstOnRaw C i ((activeOrIds C.gates (List.ofFn fun j : Fin 24 => decide (j = i))).min' pos) := by
  let w := List.ofFn fun j : Fin 24 => decide (j=i)
  let S := activeOrIds C.gates w
  have yes : S.Nonempty := pos
  let k := S.min' yes
  refine ⟨(activeOrIds_mem C.gates w k).mp (S.min'_mem yes),?_⟩
  intro j hj
  cases h : (trueOrFlags C.gates w).getD j false with
  | false => rfl
  | true =>
    let z : Fin C.gates.length := ⟨j,hj.trans k.isLt⟩
    have hz : z ∈ S := (activeOrIds_mem C.gates w z).mpr h
    exact False.elim (Nat.not_le_of_lt hj (S.min'_le z hz))

private theorem first_reads (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {i : Fin 24} {k : Fin C.gates.length} (h : firstOnRaw C i k) : i.val ∈ readAt C.gates 24 k.val := by
  let w := List.ofFn (fun j : Fin 24 => decide (j = i))
  have hi : k ∈ activeOrIds C.gates w := (activeOrIds_mem ..).mpr h.1
  obtain ⟨a,read,on⟩ := (activeOrIds_iff_final_parent C.gates w k).mp hi
  have len : w.length = 24 := by simp [w]
  rw [len] at read
  have singleton (t : ℕ) : w.getD t false = true ↔ t = i.val := by
    by_cases ht : t < 24
    · simp only [w,List.getD_eq_getElem?_getD,List.getElem?_ofFn,ht,↓reduceDIte,Option.getD_some,decide_eq_true_eq,Fin.ext_iff]
    · simp [w,List.getD_eq_getElem?_getD,ht]
      omega
  exact (minimal_crown_first_singleton_raw C hm rep mini size ors w len i singleton k.val a h.1 h.2 read on) ▸ read

def sharedFirst (C : Circuit) (i : Fin 12) : Prop :=
  ∃ k : Fin C.gates.length, firstOnRaw C ⟨i.val,by omega⟩ k ∧ firstOnRaw C ⟨12+i.val,by omega⟩ k

theorem sharedFirst_of_common_min (C : Circuit) (i : Fin 12)
    (a b : Fin 24) (rowEq : a.val = i.val) (colEq : b.val = 12+i.val)
    (ha : (activeOrIds C.gates (List.ofFn fun j : Fin 24 => decide (j=a))).Nonempty)
    (hb : (activeOrIds C.gates (List.ofFn fun j : Fin 24 => decide (j=b))).Nonempty)
    (same : (activeOrIds C.gates (List.ofFn fun j : Fin 24 => decide (j=a))).min' ha =
      (activeOrIds C.gates (List.ofFn fun j : Fin 24 => decide (j=b))).min' hb) : sharedFirst C i := by
  have ra := min_is_firstOnRaw C a ha
  have rb := min_is_firstOnRaw C b hb
  rw [←same] at rb
  have aeq : a = ⟨i.val,by omega⟩ := Fin.ext rowEq
  have beq : b = ⟨12+i.val,by omega⟩ := Fin.ext colEq
  exact ⟨_,aeq ▸ ra,beq ▸ rb⟩

theorem shared_first_raw_pair (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) (i : Fin 12)
    (hi : sharedFirst C i) : ∃ k : Fin C.gates.length, readAt C.gates 24 k.val = {i.val,12+i.val} := by
  obtain ⟨k,ra,rb⟩ := hi
  have a := first_reads C hm rep mini size ors ra
  have b := first_reads C hm rep mini size ors rb
  refine ⟨k,(Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro t ht
    rcases Finset.mem_insert.mp ht with eq | rest
    · exact eq ▸ a
    · exact (Finset.mem_singleton.mp rest) ▸ b
  · have ne : i.val ≠ 12+i.val := by omega
    simpa [ne] using readAt_card_le_two C.gates 24 k.val (fun g hg => (hm g hg).2)

theorem compress_shared_first_labels (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (L : Finset (Fin 12)) (shared : ∀ i ∈ L, sharedFirst C i) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + L.card ≤ C.size ∧
      (D.gates.filter isOrGate).length + L.card ≤ (C.gates.filter isOrGate).length ∧
      ∀ s : Finset (Fin 12), D.eval (bits s) = true ↔ 2 ≤ s.card := by
  have bound := labels_le_pairCount C L (fun i hi => shared_first_raw_pair C hm rep mini size ors i (shared i hi))
  obtain ⟨D,hd,sz,os,correct⟩ := compressed_threshold_exists C hm rep
  exact ⟨D,hd,by omega,by omega,correct⟩

end PEqualNP.Research.CrownIdentify
