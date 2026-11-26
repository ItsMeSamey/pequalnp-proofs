import Research.CrownFalseOrConflicts
import Research.CrownSubcrownMarkers

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

/-- The earlier wires read by each OR gate, in execution order, independently of input values. -/
def orInputSets : List Gate → ℕ → List (Finset ℕ)
  | [], _ => []
  | g::gs, n =>
    let later := orInputSets gs (n+1)
    if isOrGate g then (g.inputs.toFinset.filter (· < n)) :: later else later

theorem orInputSets_length (gs : List Gate) (n : ℕ) :
    (orInputSets gs n).length = (gs.filter isOrGate).length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => cases h : isOrGate g <;> simp [orInputSets,h,ih]

theorem falseOrPredecessors_length (gs : List Gate) (w : List Bool) :
    (falseOrPredecessors gs w).length = falseOrCount gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [falseOrPredecessors,falseOrCount]
    change (if falseOrAt g w then falseParents g w :: falseOrPredecessors gs (advance g w) else falseOrPredecessors gs (advance g w)).length =
      (if falseOrAt g w then 1 else 0) + falseOrCount gs (advance g w)
    cases h : falseOrAt g w <;> simp [ih,Nat.add_comm]

theorem falseOrPredecessors_sublist (gs : List Gate) (w : List Bool) :
    (falseOrPredecessors gs w).Sublist (orInputSets gs w.length) := by
  induction gs generalizing w with
  | nil => exact List.Sublist.refl _
  | cons g gs ih =>
    have ht := ih (advance g w)
    rw [advance_len] at ht
    by_cases ho : isOrGate g = true
    · rw [orInputSets,ite_eq_left ho]
      by_cases hf : falseOrAt g w = true
      · rw [falseOrPredecessors,ite_eq_left hf]
        have op : g.op = .or := by cases he : g.op <;> simp_all [isOrGate]
        simpa only [falseParents,op] using ht.cons_cons (g.inputs.toFinset.filter (· < w.length))
      · rw [falseOrPredecessors,ite_eq_right hf]
        exact ht.cons _
    · have hf : falseOrAt g w ≠ true := by simp [falseOrAt,ho]
      simpa only [orInputSets,ite_eq_right ho,falseOrPredecessors,ite_eq_right hf] using ht

theorem falseOrPredecessors_card_two (gs : List Gate) (w : List Bool) (o : ℕ)
    (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) (full : fullFalseForks gs w o) :
    ∀ p ∈ falseOrPredecessors gs w, p.card = 2 := by
  induction gs generalizing w with
  | nil => simp [falseOrPredecessors]
  | cons g gs ih =>
    obtain ⟨head,tail⟩ := full
    have ht := ih (advance g w) (fun a ha => fanin a (List.mem_cons_of_mem _ ha)) tail
    intro p hp
    by_cases hf : falseOrAt g w = true
    · rw [falseOrPredecessors,ite_eq_left hf] at hp
      rcases List.mem_cons.mp hp with rfl | mem
      · have lower := Finset.card_le_card (Finset.sdiff_subset :
            falseParents g w \ (falseLive gs (advance g w) o).erase w.length ⊆ falseParents g w)
        have exactFresh := (head hf).2
        have upper := falseParents_card g w (fanin g (List.mem_cons_self ..))
        split at upper <;> omega
      · exact ht p mem
    · exact ht p (by simpa only [falseOrPredecessors,ite_eq_right hf] using hp)

theorem crown_or_wiring (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) :
    (orInputSets C.gates 24).length = 23 ∧
    ∃ L : List (Finset ℕ), L.Sublist (orInputSets C.gates 24) ∧ L.Pairwise Disjoint ∧ (∀ p ∈ L, p.card = 2) ∧ L.length = 21 := by
  have lower := crown_size_forty_requires_twenty_three_ors C hm rep size
  have eq : (C.gates.filter isOrGate).length = 23 := by omega
  refine ⟨(orInputSets_length ..).trans eq,?_⟩
  have many := crown_many_saturated C hm rep size
  have pos : (Finset.univ.filter (fun i : Fin 12 =>
      2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i,hi⟩ := pos
  have h := (Finset.mem_filter.mp hi).2
  let w := oneEach i i
  have hw : w.length = 24 := by simp [w,oneEach]
  refine ⟨falseOrPredecessors C.gates w,hw ▸ falseOrPredecessors_sublist C.gates w,
    crown_saturated_falseOr_predecessors i C hm rep ors h,
    falseOrPredecessors_card_two _ _ _ (fun g hg => (hm g hg).2) (crown_full_false_forks i C hm rep ors h),?_⟩
  rw [falseOrPredecessors_length]
  have bal := trueOrFlags_balance C.gates w
  have bound := crown_twelve_falseOrCount i C hm rep
  change 21 ≤ falseOrCount C.gates w at bound
  change 2 ≤ (trueOrFlags C.gates w).count true at h
  omega

end PEqualNP.Research.MissingCell
