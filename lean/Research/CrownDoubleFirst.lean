import Research.CrownMaskedRigidity
import Research.CrownIndexedOrValues

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def earliestOr (C : Circuit) (i : Fin 12) (k : Fin C.gates.length) : Prop :=
  k ∈ activeOrIds C.gates (oneEach i i) ∧ ∀ j ∈ activeOrIds C.gates (oneEach i i), k ≤ j

private theorem before_earliest (C : Circuit) (i : Fin 12) (k : Fin C.gates.length)
    (h : earliestOr C i k) (j : ℕ) (lt : j < k.val) :
    (trueOrFlags C.gates (oneEach i i)).getD j false = false := by
  cases hh : (trueOrFlags C.gates (oneEach i i)).getD j false with
  | false => rfl
  | true =>
    let a : Fin C.gates.length := ⟨j,lt.trans k.isLt⟩
    exact False.elim (Nat.not_le_of_lt lt (h.2 a ((activeOrIds_mem _ _ a).mpr hh)))

private theorem zero_off (bs : List Bool) (h : bs.count true = 0) (a : ℕ) : bs.getD a false = false := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    cases b with
    | true => simp at h
    | false => cases a with
      | zero => rfl
      | succ a => exact ih (by simpa using h) a

theorem first_parent_exclusive (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (i : Fin 12) (k : Fin C.gates.length) (early : earliestOr C i k)
    (a : ℕ) (read : a ∈ readAt C.gates 24 k.val) (on : (C.wires (oneEach i i)).getD a false = true)
    (j : Fin 12) (on' : (C.wires (oneEach j j)).getD a false = true) : i=j := by
  let x := oneEach i i
  let z := List.replicate 24 false
  have xl : x.length = 24 := by simp [x,oneEach]
  have zoff (t : ℕ) : (trueOrFlags C.gates z).getD t false = false :=
    zero_off _ (crown_allzero_no_or C hm rep size ors) _
  obtain ⟨hit,cold⟩ := first_parent_masked C.gates x z (by simp [xl,z]) k.val
    ((activeOrIds_mem _ _ _).mp early.1) (before_earliest C i k early) zoff a (xl ▸ read) on
  exact trigger_unique_on_actual_diagonals C hm a i j hit cold on'

theorem double_first_gate_exclusive (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (i j : Fin 12) (ne : i ≠ j) (k : Fin C.gates.length) (hi : earliestOr C i k) (hj : earliestOr C j k) :
    Finset.univ.filter (fun d : Fin 12 => k ∈ activeOrIds C.gates (oneEach d d)) = {i,j} := by
  classical
  have parent (d : Fin 12) (on : k ∈ activeOrIds C.gates (oneEach d d)) :
      ∃ a ∈ readAt C.gates 24 k.val, (C.wires (oneEach d d)).getD a false = true := by
    have ht := (activeOrIds_iff_final_parent _ _ k).mp on
    have dl : (oneEach d d).length = 24 := by simp [oneEach]
    rw [dl] at ht
    exact ht
  obtain ⟨a,ha,ax⟩ := parent i hi.1
  obtain ⟨b,hb,bx⟩ := parent j hj.1
  have ab : a ≠ b := by
    intro eq
    exact ne (first_parent_exclusive C hm rep size ors i k hi a ha ax j (eq ▸ bx))
  have cover : ({a,b} : Finset ℕ) = readAt C.gates 24 k.val := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ha
      · exact Finset.mem_singleton.mp ht ▸ hb
    · simpa [ab] using readAt_card_le_two C.gates 24 k.val (fun g hg => (hm g hg).2)
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro active
    obtain ⟨c,hc,cx⟩ := parent d active
    rw [←cover] at hc
    rcases Finset.mem_insert.mp hc with eq | mem
    · subst c
      exact Or.inl (first_parent_exclusive C hm rep size ors i k hi a ha ax d cx).symm
    · have eq := Finset.mem_singleton.mp mem
      subst c
      exact Or.inr (first_parent_exclusive C hm rep size ors j k hj b hb bx d cx).symm
  · rintro (rfl | rfl)
    · exact hi.1
    · exact hj.1

end PEqualNP.Research.MissingCell
