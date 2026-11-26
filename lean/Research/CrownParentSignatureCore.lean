import Research.CrownIndexedOrValues

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

private theorem parent_active (C : Circuit) (i : Fin 12) (k : Fin C.gates.length) (a : ℕ)
    (read : a ∈ readAt C.gates 24 k.val) (on : (C.wires (oneEach i i)).getD a false = true) :
    k ∈ activeOrIds C.gates (oneEach i i) := by
  apply (activeOrIds_iff_final_parent ..).mpr
  refine ⟨a,?_,on⟩
  have len : (oneEach i i).length = 24 := by simp [oneEach]
  rw [len]
  exact read

def PriorOverlap (C : Circuit) : Prop := ∀ (i j : Fin 12), i ≠ j → ∀ (k : Fin C.gates.length) (a : ℕ),
    a ∈ readAt C.gates 24 k.val → (C.wires (oneEach i i)).getD a false = true →
    (C.wires (oneEach j j)).getD a false = true →
    ∃ e : Fin C.gates.length, e < k ∧ e ∈ activeOrIds C.gates (oneEach i i) ∧
      e ∈ activeOrIds C.gates (oneEach j j)

theorem parent_signature_equal_of_overlap (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (overlap : PriorOverlap C)
    (i j : Fin 12) (k : Fin C.gates.length) (a : ℕ) (read : a ∈ readAt C.gates 24 k.val)
    (ax : (C.wires (oneEach i i)).getD a false = true)
    (ay : (C.wires (oneEach j j)).getD a false = true) :
    trueOrFlags C.gates (oneEach i i) = trueOrFlags C.gates (oneEach j j) := by
  classical
  by_cases ne : i=j
  · subst j; rfl
  obtain ⟨e,ek,ei,ej⟩ := overlap i j ne k a read ax ay
  let P : Finset (Fin C.gates.length) := {e,k}
  have sz : P.card = 2 := by simp [P,ne_of_lt ek]
  have fix (v : Fin 12) (ev : e ∈ activeOrIds C.gates (oneEach v v))
      (on : (C.wires (oneEach v v)).getD a false = true) : P = activeOrIds C.gates (oneEach v v) := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ev
      · exact Finset.mem_singleton.mp ht ▸ parent_active C v k a read on
    · rw [sz,activeOrIds_card]
      have h := crown_trueOrFlags_le v C hm rep
      omega
  exact flags_eq_of_ids_eq _ _ _ ((fix i ei ax).symm.trans (fix j ej ay))

theorem parent_diagonals_bound_of_overlap (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) (overlap : PriorOverlap C)
    (k : Fin C.gates.length) (a : ℕ) (read : a ∈ readAt C.gates 24 k.val) :
    (Finset.univ.filter (fun i : Fin 12 => (C.wires (oneEach i i)).getD a false)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun i : Fin 12 => (C.wires (oneEach i i)).getD a false)
  change A.card ≤ 2
  by_cases ne : A.Nonempty
  · obtain ⟨i,hi⟩ := ne
    have ht := (Finset.mem_filter.mp hi).2
    have active := parent_active C i k a read ht
    have pos : 0 < (trueOrFlags C.gates (oneEach i i)).count true := by
      rw [←activeOrIds_card]
      exact Finset.card_pos.mpr ⟨k,active⟩
    apply le_trans _ (crown_positive_signature_at_most_two C hm rep size ors _ pos)
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      parent_signature_equal_of_overlap C hm rep ors overlap j i k a read (Finset.mem_filter.mp hj).2 ht⟩
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]

theorem gate_signatures_bound_of_overlap (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (overlap : PriorOverlap C) (k : Fin C.gates.length) :
    ((Finset.univ.filter (fun i : Fin 12 => k ∈ activeOrIds C.gates (oneEach i i))).image
      (fun i => trueOrFlags C.gates (oneEach i i))).card ≤ 2 := by
  classical
  let R := readAt C.gates 24 k.val
  let on (a : ℕ) (i : Fin 12) := (C.wires (oneEach i i)).getD a false = true
  let sig (i : Fin 12) := trueOrFlags C.gates (oneEach i i)
  let key (a : ℕ) : List Bool := if h : ∃ i, on a i then sig h.choose else []
  apply le_trans _ ((Finset.card_image_le : (R.image key).card ≤ R.card).trans
    (readAt_card_le_two _ _ _ (fun g hg => (hm g hg).2)))
  apply Finset.card_le_card
  intro b hb
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨a,ha,hit⟩ := (activeOrIds_iff_final_parent C.gates (oneEach i i) k).mp (Finset.mem_filter.mp hi).2
  have len : (oneEach i i).length = 24 := by simp [oneEach]
  rw [len] at ha
  have ex : ∃ t, on a t := ⟨i,hit⟩
  refine Finset.mem_image.mpr ⟨a,ha,?_⟩
  simp only [key,dite_eq_left ex]
  exact parent_signature_equal_of_overlap C hm rep ors overlap ex.choose i k a ha ex.choose_spec hit

theorem gate_diagonals_bound_of_overlap (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) (overlap : PriorOverlap C)
    (k : Fin C.gates.length) :
    (Finset.univ.filter (fun i : Fin 12 => k ∈ activeOrIds C.gates (oneEach i i))).card ≤ 4 := by
  classical
  let R := readAt C.gates 24 k.val
  let S (a : ℕ) := Finset.univ.filter (fun i : Fin 12 => (C.wires (oneEach i i)).getD a false)
  refine le_trans (b := (R.biUnion S).card) ?_ ?_
  · apply Finset.card_le_card
    intro i hi
    obtain ⟨a,ha,hit⟩ := (activeOrIds_iff_final_parent C.gates (oneEach i i) k).mp (Finset.mem_filter.mp hi).2
    have len : (oneEach i i).length = 24 := by simp [oneEach]
    rw [len] at ha
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩⟩
  · calc
      _ ≤ ∑ a ∈ R, (S a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ R, 2 := Finset.sum_le_sum (fun a ha => parent_diagonals_bound_of_overlap C hm rep size ors overlap k a ha)
      _ ≤ 4 := by
        have b := readAt_card_le_two C.gates 24 k.val (fun g hg => (hm g hg).2)
        change R.card ≤ 2 at b
        simp
        omega

end PEqualNP.Research.MissingCell
