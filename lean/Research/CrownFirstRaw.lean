import Research.CrownGateMinimal
import Research.CrownTwoWitnessRigidity
import Research.CrownDoubleFirst

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open PEqualNP.Outside.L_meta_2668

theorem minimal_crown_masked_trigger_raw (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (mini : crownSizeMinimal C) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (i : Fin 12) (a : ℕ)
    (hit : (maskedWires C.gates (oneEach i i)).getD a false = true)
    (cold : (maskedWires C.gates (List.replicate 24 false)).getD a false = false) :
    a = i.val ∨ a = 12+i.val := by
  have len : (oneEach i i).length = 24 := by simp [oneEach]
  have on : val C (oneEach i i) a = true :=
    (masked_true_wire_rigid C.gates _ _ rfl (fun g hg => (hm g hg).1) a hit).symm.trans hit
  by_cases lt : a < 24
  · exact (raw_oneEach_on i i a).mp ((val_input len lt).symm.trans on)
  have valid : a < 24+C.gates.length := by
    by_contra! no
    rw [val_ge len no] at on
    contradiction
  let r := a-24
  have ar : 24+r = a := by dsimp [r]; omega
  have hr : r < C.gates.length := by omega
  obtain ⟨u,v,ne,hot⟩ := minimal_crown_offdiag_needed C hm rep mini ors r hr
  rw [ar] at hot
  obtain ⟨z,zl,copyEq⟩ := masked_trigger_raw_or_diagonal C hm a i hit cold u v ne hot
  apply False.elim (minimal_crown_no_raw_copy C hm rep mini ors r z hr zl ?_)
  intro x y
  rw [ar]
  exact copyEq _ (by simp [oneEach])

private theorem zero_flags_off (bs : List Bool) (h : bs.count true = 0) (a : ℕ) : bs.getD a false = false := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    cases b with
    | true => simp at h
    | false => cases a with
      | zero => rfl
      | succ a => exact ih (by simpa using h) a

theorem minimal_crown_first_parent_raw (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (mini : crownSizeMinimal C) (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (i : Fin 12) (k : Fin C.gates.length) (early : earliestOr C i k)
    (a : ℕ) (read : a ∈ readAt C.gates 24 k.val) (on : (C.wires (oneEach i i)).getD a false = true) :
    a = i.val ∨ a = 12+i.val := by
  let w := oneEach i i
  let z := List.replicate 24 false
  have len : w.length = 24 := by simp [w,oneEach]
  have before (j : ℕ) (hj : j < k.val) : (trueOrFlags C.gates w).getD j false = false := by
    cases flag : (trueOrFlags C.gates w).getD j false with
    | false => rfl
    | true =>
      let h : Fin C.gates.length := ⟨j,hj.trans k.isLt⟩
      exact False.elim (Nat.not_le_of_lt hj (early.2 h ((activeOrIds_mem ..).mpr flag)))
  obtain ⟨hit,cold⟩ := first_parent_masked C.gates w z (by simp [len,z]) k.val
    ((activeOrIds_mem ..).mp early.1) before
    (zero_flags_off _ (crown_allzero_no_or C hm rep size ors)) a (len ▸ read) on
  exact minimal_crown_masked_trigger_raw C hm rep mini ors i a hit cold

end PEqualNP.Research.MissingCell
