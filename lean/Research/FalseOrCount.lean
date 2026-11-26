import Research.ZeroCellDegree

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem falseParents_false (g : Gate) (w : List Bool) (i : ℕ)
    (hf : g.op.eval (g.inputs.map fun k => w.getD k false) = false)
    (hi : i ∈ falseParents g w) : w.getD i false = false := by
  cases hop : g.op <;> simp only [falseParents, hop] at hi
  · cases he : g.inputs.find? (fun k => !(w.getD k false)) with
    | none => simp only [he, Finset.notMem_empty] at hi
    | some k =>
      simp only [he] at hi
      split at hi
      · have hik := Finset.mem_singleton.mp hi
        subst i
        simpa using List.find?_some he
      · simp at hi
  · have hmem := List.mem_toFinset.mp (Finset.mem_filter.mp hi).1
    rw [hop] at hf
    simp only [GateOp.eval, List.any_map, List.any_eq_false] at hf
    simpa using hf i hmem
  all_goals simp at hi

theorem falseLive_false (gs : List Gate) (w : List Bool) (o i : ℕ)
    (hi : i ∈ falseLive gs w o) : w.getD i false = false := by
  induction gs generalizing w i with
  | nil =>
    simp only [falseLive] at hi
    split at hi
    next h =>
      rw [Finset.mem_singleton.mp hi]
      exact h.2
    next => simp at hi
  | cons g gs ih =>
    have hb := falseLive_lt (g :: gs) w o i hi
    by_cases hm : w.length ∈ falseLive gs (advance g w) o
    · simp only [falseLive, ite_eq_left hm, Finset.mem_union, Finset.mem_erase] at hi
      rcases hi with ⟨_,ht⟩ | hp
      · simpa only [getD_advance_lt g w i hb] using ih (advance g w) i ht
      · apply falseParents_false g w i _ hp
        simpa only [getD_advance_eq] using ih (advance g w) w.length hm
    · simp only [falseLive, ite_eq_right hm] at hi
      simpa only [getD_advance_lt g w i hb] using ih (advance g w) i hi

/-- Number of OR gates evaluating to false when execution starts with wire values w. -/
def falseOrCount : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w =>
    (if isOrGate g && !(g.op.eval (g.inputs.map fun i => w.getD i false)) then 1 else 0) +
      falseOrCount gs (advance g w)

theorem falseLive_falseOrCount (gs : List Gate) (w : List Bool) (o : ℕ)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (falseLive gs w o).card ≤ falseOrCount gs w + 1 := by
  induction gs generalizing w with
  | nil =>
    simp only [falseLive,falseOrCount]
    split <;> simp
  | cons g gs ih =>
    let t := falseLive gs (advance g w) o
    have ht : t.card ≤ falseOrCount gs (advance g w) + 1 :=
      ih (advance g w) (fun k hk => h k (List.mem_cons_of_mem _ hk))
    have hp := falseParents_card g w (h g (List.mem_cons_self ..))
    change (if w.length ∈ t then t.erase w.length ∪ falseParents g w else t).card ≤ _
    by_cases hm : w.length ∈ t
    · rw [ite_eq_left hm]
      have hf := falseLive_false gs (advance g w) o w.length hm
      rw [getD_advance_eq] at hf
      have he := Finset.card_erase_add_one hm
      have hu := Finset.card_union_le (t.erase w.length) (falseParents g w)
      simp only [falseOrCount, hf, Bool.not_false, Bool.and_true]
      cases hb : isOrGate g <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hp ⊢ <;> omega
    · rw [ite_eq_right hm]
      simp only [falseOrCount]
      omega

theorem zeroCell_degree_falseOrCount {n m : ℕ} (A : Fin n → Fin m → Bool)
    (i : Fin n) (j : Fin m) (C : Circuit) (hm : Monotone2 C)
    (hr : Represents A C) (hz : A i j = false) :
    (Finset.univ.filter (fun u => A u j)).card + (Finset.univ.filter (fun v => A i v)).card ≤
      falseOrCount C.gates (oneEach i j) + 1 :=
  (zeroCell_degree_falseLive A i j C hm hr hz).trans
    (falseLive_falseOrCount _ _ _ (fun g hg => (hm g hg).2))

theorem crown_twelve_falseOrCount (i : Fin 12) (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) :
    21 ≤ falseOrCount C.gates (oneEach i i) := by
  have h := zeroCell_degree_falseOrCount (fun u v : Fin 12 => decide (u ≠ v)) i i C hm hr (by simp)
  have hd : ∀ i : Fin 12, (Finset.univ.filter (fun u : Fin 12 => decide (u ≠ i))).card = 11 ∧
      (Finset.univ.filter (fun v : Fin 12 => decide (i ≠ v))).card = 11 := by decide
  rw [(hd i).1,(hd i).2] at h
  omega

end PEqualNP.Research.MissingCell
