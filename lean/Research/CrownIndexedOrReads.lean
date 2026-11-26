import Research.CrownOrWiring
import Research.CrownDistinctSaturation

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def orReads (g : Gate) (n : ℕ) : Finset ℕ :=
  if isOrGate g then g.inputs.toFinset.filter (· < n) else ∅

def readAt : List Gate → ℕ → ℕ → Finset ℕ
  | [], _, _ => ∅
  | g::_, n, 0 => orReads g n
  | _::gs,n,k+1 => readAt gs (n+1) k

def activeOrIds : (gs : List Gate) → List Bool → Finset (Fin gs.length)
  | [],_ => ∅
  | g::gs,w =>
    let tail := (activeOrIds gs (advance g w)).map (Fin.succEmb _)
    if isOrGate g && gateBool g w then insert 0 tail else tail

theorem activeOrIds_card (gs : List Gate) (w : List Bool) :
    (activeOrIds gs w).card = (trueOrFlags gs w).count true := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have h0 : (0 : Fin (gs.length+1)) ∉ (activeOrIds gs (advance g w)).map (Fin.succEmb _) := by simp
    let t := (activeOrIds gs (advance g w)).map (Fin.succEmb _)
    change (if isOrGate g && gateBool g w then insert 0 t else t).card =
      ((isOrGate g && gateBool g w) :: trueOrFlags gs (advance g w)).count true
    cases hb : isOrGate g && gateBool g w <;> simp [t,h0,ih]

theorem activeOrIds_mem (gs : List Gate) (w : List Bool) (i : Fin gs.length) :
    i ∈ activeOrIds gs w ↔ (trueOrFlags gs w).getD i.val false = true := by
  induction gs generalizing w with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    let b := isOrGate g && gateBool g w
    let t := (activeOrIds gs (advance g w)).map (Fin.succEmb _)
    change i ∈ (if b then insert 0 t else t) ↔ (b :: trueOrFlags gs (advance g w)).getD i.val false = true
    refine Fin.cases ?_ (fun j => ?_) i
    · cases hb : b <;> simp [t]
    · cases hb : b <;> simp [t,ih]

theorem flags_eq_of_ids_eq (gs : List Gate) (x y : List Bool) (h : activeOrIds gs x = activeOrIds gs y) :
    trueOrFlags gs x = trueOrFlags gs y := by
  apply List.ext_getElem
  · simp [trueOrFlags_length]
  · intro i hx hy
    let j : Fin gs.length := ⟨i,by simpa only [trueOrFlags_length] using hx⟩
    have eq : j ∈ activeOrIds gs x ↔ j ∈ activeOrIds gs y := by rw [h]
    rw [activeOrIds_mem,activeOrIds_mem] at eq
    change (trueOrFlags gs x).getD i false = true ↔ (trueOrFlags gs y).getD i false = true at eq
    simpa [List.getD_eq_getElem?_getD,hx,hy] using eq

private theorem false_read_mem_or_empty (gs : List Gate) (w : List Bool) (k : ℕ)
    (off : (trueOrFlags gs w).getD k false = false) :
    readAt gs w.length k = ∅ ∨ readAt gs w.length k ∈ falseOrPredecessors gs w := by
  induction gs generalizing k w with
  | nil => exact Or.inl rfl
  | cons g gs ih =>
    cases k with
    | zero =>
      by_cases ho : isOrGate g = true
      · have op : g.op = .or := by cases hg : g.op <;> simp_all [isOrGate]
        have hv : gateBool g w = false := by simpa only [gateBool,trueOrFlags,List.getD_cons_zero,ho,Bool.true_and] using off
        have hf : falseOrAt g w = true := by
          change (isOrGate g && !gateBool g w) = true
          simp [ho,hv]
        exact Or.inr (by simp only [readAt,orReads,ho,↓reduceIte,falseOrPredecessors,hf,falseParents,op,List.mem_cons_self])
      · exact Or.inl (by simp [readAt,orReads,ho])
    | succ k =>
      have lt := ih (advance g w) k (by simpa only [trueOrFlags,List.getD_cons_succ] using off)
      rw [advance_len] at lt
      rcases lt with empty | mem
      · exact Or.inl empty
      · refine Or.inr ?_
        change readAt gs (w.length+1) k ∈ falseOrPredecessors (g::gs) w
        rw [falseOrPredecessors]
        split <;> simp [mem]

theorem false_reads_disjoint (gs : List Gate) (w : List Bool)
    (pairwise : (falseOrPredecessors gs w).Pairwise Disjoint) (i j : ℕ) (lt : i<j)
    (fi : (trueOrFlags gs w).getD i false = false) (fj : (trueOrFlags gs w).getD j false = false) :
    Disjoint (readAt gs w.length i) (readAt gs w.length j) := by
  induction gs generalizing w i j with
  | nil => simp [readAt]
  | cons g gs ih =>
    cases j with
    | zero => omega
    | succ j =>
      have hj : (trueOrFlags gs (advance g w)).getD j false = false := fj
      cases i with
      | zero =>
        by_cases ho : isOrGate g = true
        · have op : g.op = .or := by cases hg : g.op <;> simp_all [isOrGate]
          have hv : gateBool g w = false := by simpa only [gateBool,trueOrFlags,List.getD_cons_zero,ho,Bool.true_and] using fi
          have hf : falseOrAt g w = true := by
            change (isOrGate g && !gateBool g w) = true
            simp [ho,hv]
          rw [falseOrPredecessors,ite_eq_left hf,List.pairwise_cons] at pairwise
          have hmem := false_read_mem_or_empty _ _ _ hj
          rw [advance_len] at hmem
          rcases hmem with empty | mem
          · simp [readAt,empty]
          · simpa only [readAt,orReads,ho,↓reduceIte,falseParents,op] using pairwise.1 _ mem
        · simp [readAt,orReads,ho]
      | succ i =>
        have pi : (falseOrPredecessors gs (advance g w)).Pairwise Disjoint := by
          rw [falseOrPredecessors] at pairwise
          split at pairwise
          · exact (List.pairwise_cons.mp pairwise).2
          · exact pairwise
        have res := ih (advance g w) pi i j (by omega) (by exact fi) hj
        simpa only [readAt,advance_len] using res

theorem crown_inactive_pair_disjoint (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (k : Fin 12)
    (active : (trueOrFlags C.gates (oneEach k k)).count true = 2)
    (a b : Fin C.gates.length) (ab : a ≠ b) (na : a ∉ activeOrIds C.gates (oneEach k k))
    (nb : b ∉ activeOrIds C.gates (oneEach k k)) :
    Disjoint (readAt C.gates 24 a.val) (readAt C.gates 24 b.val) := by
    have pw := crown_saturated_falseOr_predecessors k C hm rep ors (by omega)
    have off (x : Fin C.gates.length) (nx : x ∉ activeOrIds C.gates (oneEach k k)) : (trueOrFlags C.gates (oneEach k k)).getD x.val false = false := by
      cases h : (trueOrFlags C.gates (oneEach k k)).getD x.val false with
      | false => rfl
      | true => exact False.elim (nx ((activeOrIds_mem ..).mpr h))
    have ord : a.val < b.val ∨ b.val < a.val := by
      have ne := fun he => ab (Fin.ext he)
      omega
    rcases ord with lt | gt
    · have eq : (oneEach k k).length = 24 := by simp [oneEach]
      exact eq ▸ false_reads_disjoint _ _ pw _ _ lt (off a na) (off b nb)
    · have eq : (oneEach k k).length = 24 := by simp [oneEach]
      exact eq ▸ (false_reads_disjoint _ _ pw _ _ gt (off b nb) (off a na)).symm

theorem crown_indexed_or_covers (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    ∃ P Q : Finset (Fin C.gates.length), P.card = 2 ∧ Q.card = 2 ∧ P ≠ Q ∧
      ∀ a b : Fin C.gates.length, a ≠ b →
        (a ∉ P → b ∉ P → Disjoint (readAt C.gates 24 a.val) (readAt C.gates 24 b.val)) ∧
        (a ∉ Q → b ∉ Q → Disjoint (readAt C.gates 24 a.val) (readAt C.gates 24 b.val)) := by
  obtain ⟨i,j,ti,tj,diff⟩ := crown_distinct_saturated_signatures C hm rep size ors
  let ids (i : Fin 12) := activeOrIds C.gates (oneEach i i)
  exact ⟨ids i,ids j,(activeOrIds_card ..).trans ti,(activeOrIds_card ..).trans tj,
    fun eq => diff (flags_eq_of_ids_eq _ _ _ eq),fun a b ab => ⟨crown_inactive_pair_disjoint C hm rep ors i ti a b ab,crown_inactive_pair_disjoint C hm rep ors j tj a b ab⟩⟩

theorem readAt_card_le_two (gs : List Gate) (n k : ℕ) (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (readAt gs n k).card ≤ 2 := by
  induction gs generalizing n k with
  | nil => simp [readAt]
  | cons g gs ih =>
    cases k with
    | zero =>
      rw [readAt,orReads]
      split
      · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
          ((List.toFinset_card_le _).trans (fanin g (List.mem_cons_self ..)))
      · simp
    | succ k => exact ih _ _ (fun a ha => fanin a (List.mem_cons_of_mem _ ha))

end PEqualNP.Research.MissingCell
