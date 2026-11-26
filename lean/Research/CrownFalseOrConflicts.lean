import Research.CrownFalseOrSaturation

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Chronological predecessor sets of the OR gates that evaluate false. -/
def falseOrPredecessors : List Gate → List Bool → List (Finset ℕ)
  | [], _ => []
  | g::gs, w =>
    let tail := falseOrPredecessors gs (advance g w)
    if falseOrAt g w then (falseParents g w) :: tail else tail

private theorem claimed_is_live (gs : List Gate) (w : List Bool) (o : ℕ) (full : fullFalseForks gs w o)
    (P : Finset ℕ) (hp : P ∈ falseOrPredecessors gs w) (i : ℕ) (hi : i ∈ P) (hb : i < w.length) :
    i ∈ falseLive gs w o := by
  induction gs generalizing w with
  | nil => simp [falseOrPredecessors] at hp
  | cons g gs ih =>
    obtain ⟨head,tail⟩ := full
    have hin (ht : P ∈ falseOrPredecessors gs (advance g w)) : i ∈ falseLive (g::gs) w o := by
      have h := ih (advance g w) tail ht (by rw [advance_len]; omega)
      by_cases used : w.length ∈ falseLive gs (advance g w) o <;>
        simp [falseLive,used,h,Nat.ne_of_lt hb]
    by_cases ho : falseOrAt g w = true
    · rw [falseOrPredecessors,ite_eq_left ho] at hp
      rcases List.mem_cons.mp hp with rfl | ht
      · simp [falseLive,(head ho).1,hi]
      · exact hin ht
    · rw [falseOrPredecessors,ite_eq_right ho] at hp
      exact hin hp

theorem fullFalseForks_disjoint (gs : List Gate) (w : List Bool) (o : ℕ)
    (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2) (full : fullFalseForks gs w o) :
    (falseOrPredecessors gs w).Pairwise Disjoint := by
  induction gs generalizing w with
  | nil => simp [falseOrPredecessors]
  | cons g gs ih =>
    obtain ⟨head,tail⟩ := full
    have tr := ih (advance g w) (fun a ha => fanin a (List.mem_cons_of_mem _ ha)) tail
    by_cases ho : falseOrAt g w = true
    · rw [falseOrPredecessors,ite_eq_left ho,List.pairwise_cons]
      refine ⟨?_,tr⟩
      intro P hp
      have hc := (head ho).2
      let t := falseLive gs (advance g w) o
      have sz := falseParents_card g w (fanin g (List.mem_cons_self ..))
      have up : (falseParents g w).card ≤ 2 := by split at sz <;> omega
      have dis : Disjoint (falseParents g w) (t.erase w.length) :=
        Finset.sdiff_eq_self_iff_disjoint.mp (Finset.eq_of_subset_of_card_le Finset.sdiff_subset (by
          change (falseParents g w).card ≤ (falseParents g w \ (falseLive gs (advance g w) o).erase w.length).card
          omega))
      apply Finset.disjoint_left.mpr
      intro i hg hi
      have hb := falseParents_lt g w i hg
      have member := claimed_is_live gs (advance g w) o tail P hp i hi (by rw [advance_len]; omega)
      exact Finset.disjoint_left.mp dis hg (Finset.mem_erase.mpr ⟨Nat.ne_of_lt hb,member⟩)
    · simpa only [falseOrPredecessors,ite_eq_right ho] using tr

theorem crown_saturated_falseOr_predecessors (i : Fin 12) (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (total : (C.gates.filter isOrGate).length ≤ 23)
    (active : 2 ≤ (trueOrFlags C.gates (oneEach i i)).count true) :
    (falseOrPredecessors C.gates (oneEach i i)).Pairwise Disjoint :=
  fullFalseForks_disjoint _ _ _ (fun g hg => (hm g hg).2)
    (crown_full_false_forks i C hm rep total active)

end PEqualNP.Research.MissingCell
