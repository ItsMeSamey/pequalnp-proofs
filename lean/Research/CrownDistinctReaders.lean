import Research.CrownIndexedOrValues

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def readUnion : List (Finset ℕ) → Finset ℕ
  | [] => ∅
  | x::xs => x ∪ readUnion xs

theorem readUnion_mem (L : List (Finset ℕ)) (a : ℕ) :
    a ∈ readUnion L ↔ ∃ p ∈ L, a ∈ p := by
  induction L with
  | nil => simp [readUnion]
  | cons p ps ih => simp [readUnion,ih]

private theorem readUnion_pairs (L : List (Finset ℕ)) (dis : L.Pairwise Disjoint)
    (two : ∀ p ∈ L, p.card = 2) : (readUnion L).card = 2*L.length := by
  induction L with
  | nil => simp [readUnion]
  | cons p ps ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp dis
    have hd : Disjoint p (readUnion ps) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨q,hq,mem⟩ := (readUnion_mem ..).mp hb
      exact Finset.disjoint_left.mp (head q hq) ha mem
    rw [readUnion,Finset.card_union_of_disjoint hd,two p (by simp),ih tail (fun x hx => two x (by simp [hx]))]
    simp [Nat.mul_succ,Nat.add_comm]

private theorem falseParents_final (gs : List Gate) (w : List Bool) (p : Finset ℕ)
    (hp : p ∈ falseOrPredecessors gs w) (a : ℕ) (ha : a ∈ p) :
    ((Circuit.mk gs 0).wires w).getD a false = false := by
  induction gs generalizing w with
  | nil => simp [falseOrPredecessors] at hp
  | cons g gs ih =>
    by_cases hf : falseOrAt g w = true
    · rw [falseOrPredecessors,ite_eq_left hf] at hp
      rcases List.mem_cons.mp hp with rfl | ht
      · have eq : ((Circuit.mk (g::gs) 0).wires w).getD a false = w.getD a false := by
          have keep (t : List Gate) (x : List Bool) (h : a < x.length) :
              ((Circuit.mk t 0).wires x).getD a false = x.getD a false := by
            induction t generalizing x with
            | nil => rfl
            | cons b bs step =>
              change ((Circuit.mk bs 0).wires (advance b x)).getD a false = _
              rw [step _ (by rw [advance_len]; omega),getD_advance_lt b x a h]
          exact keep _ _ (falseParents_lt g w a ha)
        have he : g.op.eval (g.inputs.map fun k => w.getD k false) = false := by
          exact (show isOrGate g = true ∧ _ from (by simpa [falseOrAt] using hf)).2
        exact eq.trans (falseParents_false g w a he ha)
      · exact ih (advance g w) ht
    · rw [falseOrPredecessors,ite_eq_right hf] at hp
      exact ih (advance g w) hp

private theorem readAt_in_union (gs : List Gate) (n k a : ℕ) (h : a ∈ readAt gs n k) :
    a ∈ readUnion (orInputSets gs n) := by
  induction gs generalizing n k with
  | nil => simp [readAt] at h
  | cons g gs ih =>
    cases k with
    | zero =>
      by_cases ho : isOrGate g = true
      · simp [readAt,orReads,ho] at h
        simp [orInputSets,ho,readUnion,h]
      · simp [readAt,orReads,ho] at h
    | succ k =>
      have m := ih (n+1) k h
      by_cases ho : isOrGate g = true <;> simp [orInputSets,ho,readUnion,m]

private theorem saturated_false_read_count (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (i : Fin 12)
    (twoI : (trueOrFlags C.gates (oneEach i i)).count true = 2) :
    (readUnion (falseOrPredecessors C.gates (oneEach i i))).card = 42 := by
  let w := oneEach i i
  let L := falseOrPredecessors C.gates w
  have lower := crown_twelve_falseOrCount i C hm rep
  have bal := trueOrFlags_balance C.gates w
  have count : L.length = 21 := by
    rw [show L.length = falseOrCount C.gates w from falseOrPredecessors_length ..]
    change 21 ≤ falseOrCount C.gates w at lower
    change (trueOrFlags C.gates w).count true = 2 at twoI
    omega
  have size : (readUnion L).card = 42 := by
    rw [readUnion_pairs L (crown_saturated_falseOr_predecessors i C hm rep ors (by omega))
      (falseOrPredecessors_card_two _ _ _ (fun g hg => (hm g hg).2)
        (crown_full_false_forks i C hm rep ors (by omega))),count]
  exact size

theorem disjoint_saturation_forty_four_parents (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (i j : Fin 12)
    (twoI : (trueOrFlags C.gates (oneEach i i)).count true = 2)
    (twoJ : (trueOrFlags C.gates (oneEach j j)).count true = 2)
    (dis : Disjoint (activeOrIds C.gates (oneEach i i)) (activeOrIds C.gates (oneEach j j))) :
    44 ≤ (readUnion (orInputSets C.gates 24)).card := by
  let w := oneEach i i
  have len : w.length = 24 := by simp [w,oneEach]
  let L := falseOrPredecessors C.gates w
  let U := readUnion (orInputSets C.gates 24)
  have size : (readUnion L).card = 42 := saturated_false_read_count C hm rep ors i twoI
  have sub : readUnion L ⊆ U := by
    intro a ha
    obtain ⟨p,hp,ap⟩ := (readUnion_mem ..).mp ha
    have mem := (falseOrPredecessors_sublist C.gates w).subset hp
    exact (readUnion_mem ..).mpr ⟨p,len ▸ mem,ap⟩
  have cardI : (activeOrIds C.gates w).card = 2 := (activeOrIds_card ..).trans twoI
  obtain ⟨b,c,bc,ids⟩ := Finset.card_eq_two.mp cardI
  have hb : b ∈ activeOrIds C.gates w := by simp [ids]
  have hc : c ∈ activeOrIds C.gates w := by simp [ids]
  obtain ⟨a,ar,av⟩ := (activeOrIds_iff_final_parent C.gates w b).mp hb
  obtain ⟨e,er,ev⟩ := (activeOrIds_iff_final_parent C.gates w c).mp hc
  have ap := readAt_in_union _ _ _ _ ar
  have ep := readAt_in_union _ _ _ _ er
  rw [len] at ar er ap ep
  have sep := crown_inactive_pair_disjoint C hm rep ors j twoJ b c bc
    (Finset.disjoint_left.mp dis hb) (Finset.disjoint_left.mp dis hc)
  have ae : a ≠ e := fun eq => Finset.disjoint_left.mp sep ar (eq ▸ er)
  have fresh (x : ℕ) (hx : ((Circuit.mk C.gates 0).wires w).getD x false = true) :
      x ∉ readUnion L := by
    intro mem
    obtain ⟨p,hp,px⟩ := (readUnion_mem ..).mp mem
    have h := falseParents_final C.gates w p hp x px
    simp_all
  have bound := Finset.card_le_card
    (show insert a (insert e (readUnion L)) ⊆ U from
      Finset.insert_subset ap (Finset.insert_subset ep sub))
  rw [Finset.card_insert_of_notMem (by simp [ae,fresh a av]),
      Finset.card_insert_of_notMem (fresh e ev),size] at bound
  exact bound

theorem saturated_forty_three_parents (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (i : Fin 12)
    (twoI : (trueOrFlags C.gates (oneEach i i)).count true = 2) :
    43 ≤ (readUnion (orInputSets C.gates 24)).card := by
  let w := oneEach i i
  have len : w.length = 24 := by simp [w,oneEach]
  let L := falseOrPredecessors C.gates w
  have size : (readUnion L).card = 42 := saturated_false_read_count C hm rep ors i twoI
  have cardI : (activeOrIds C.gates w).card = 2 := (activeOrIds_card ..).trans twoI
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < (activeOrIds C.gates w).card by omega)
  obtain ⟨a,ar,av⟩ := (activeOrIds_iff_final_parent C.gates w b).mp hb
  have ap := readAt_in_union _ _ _ _ ar
  rw [len] at ap
  have sub : readUnion L ⊆ readUnion (orInputSets C.gates 24) := by
    intro x hx
    obtain ⟨p,hp,px⟩ := (readUnion_mem ..).mp hx
    have mem := (falseOrPredecessors_sublist C.gates w).subset hp
    exact (readUnion_mem ..).mpr ⟨p,len ▸ mem,px⟩
  have fresh : a ∉ readUnion L := by
    intro mem
    obtain ⟨p,hp,px⟩ := (readUnion_mem ..).mp mem
    have h := falseParents_final C.gates w p hp a px
    simp_all
  have bound := Finset.card_le_card (Finset.insert_subset ap sub)
  rw [Finset.card_insert_of_notMem fresh,size] at bound
  exact bound

end PEqualNP.Research.MissingCell
