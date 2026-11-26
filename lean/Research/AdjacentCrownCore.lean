import Research.AdjacentTriggers
import Research.CrownCollisionLimit

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

private theorem share_flip (C : Circuit) {a b : Fin C.gates.length}
    (h : shareOrRead C a b) : shareOrRead C b a := by
  obtain ⟨v,x,y⟩ := h
  exact ⟨v,y,x⟩

private theorem ordered_adjacent_container (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b c : Fin C.gates.length} (ac : a < c) (ab : a ≠ b) (bc : b ≠ c)
    (eab : shareOrRead C a b) (ebc : shareOrRead C b c) (eac : ¬shareOrRead C a c) :
    ∃ T : Finset ℕ, T.card ≤ 3 ∧ ∀ (i : Fin 12) (k : Fin C.gates.length),
      (trueOrFlags C.gates (oneEach i i)).count true = 2 →
      k ∈ activeOrIds C.gates (oneEach i i) →
      (∀ j ∈ activeOrIds C.gates (oneEach i i), k ≤ j) →
      ∃ v ∈ T, v ∈ readAt C.gates 24 k.val ∧ (C.wires (oneEach i i)).getD v false = true := by
  classical
  let P (j : Fin C.gates.length) := readAt C.gates 24 j.val
  have dis : Disjoint (P a) (P c) := Finset.disjoint_left.mpr (fun v hv hh => eac ⟨v,hv,hh⟩)
  obtain ⟨p,pa,pb⟩ := eab
  obtain ⟨q,qb,qc⟩ := ebc
  obtain ⟨T,card,H⟩ := CrownCollisions.adjacent_triggers P ac ab bc
    (fun j => readAt_card_le_two _ _ _ (fun g hg => (hm g hg).2)) dis
    ⟨p,Finset.mem_inter.mpr ⟨pa,pb⟩⟩ ⟨q,Finset.mem_inter.mpr ⟨qb,qc⟩⟩
  refine ⟨T,card,?_⟩
  intro i k act hk least
  let x := oneEach i i
  let S := activeOrIds C.gates x
  let on (v : ℕ) := (C.wires x).getD v false = true
  have cover {s t : Fin C.gates.length} (ne : s ≠ t) (v : ℕ) (vs : v ∈ P s) (vt : v ∈ P t) :
      s ∈ S ∨ t ∈ S := by
    by_contra! both
    exact Finset.disjoint_left.mp (crown_inactive_pair_disjoint C hm rep ors i act s t ne both.1 both.2) vs vt
  have len : x.length = 24 := by simp [x,oneEach]
  have eval (j : Fin C.gates.length) : j ∈ S ↔ ∃ v ∈ P j, on v := by
    simpa only [P,S,on,← len,Circuit.wires] using activeOrIds_iff_final_parent C.gates x j
  exact H S on k ((activeOrIds_card ..).trans act) (cover ab p pa pb)
    (cover bc q qb qc) eval hk least

theorem adjacent_trigger_container (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b c : Fin C.gates.length} (ac : a ≠ c) (ab : a ≠ b) (bc : b ≠ c)
    (eab : shareOrRead C a b) (ebc : shareOrRead C b c) (eac : ¬shareOrRead C a c) :
    ∃ T : Finset ℕ, T.card ≤ 3 ∧ ∀ (i : Fin 12) (k : Fin C.gates.length),
      (trueOrFlags C.gates (oneEach i i)).count true = 2 →
      k ∈ activeOrIds C.gates (oneEach i i) →
      (∀ j ∈ activeOrIds C.gates (oneEach i i), k ≤ j) →
      ∃ v ∈ T, v ∈ readAt C.gates 24 k.val ∧ (C.wires (oneEach i i)).getD v false = true := by
  rcases lt_or_gt_of_ne ac with h|h
  · exact ordered_adjacent_container C hm rep ors h ab bc eab ebc eac
  · exact ordered_adjacent_container C hm rep ors h bc.symm ab.symm
      (share_flip C ebc) (share_flip C eab) (fun h => eac (share_flip C h))

end PEqualNP.Research.MissingCell
