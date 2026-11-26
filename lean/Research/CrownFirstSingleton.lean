import Research.CrownFirstRaw

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
open PEqualNP.Outside.L_meta_2668

theorem masked_singleton_is_raw (C : Circuit) (hm : Monotone2 C) (a : ℕ)
    (w : List Bool) (len : w.length = 24) (z : Fin 24)
    (singleton : ∀ k, w.getD k false = true ↔ k = z.val)
    (hit : (maskedWires C.gates w).getD a false = true)
    (cold : (maskedWires C.gates (List.replicate 24 false)).getD a false = false) :
    ∀ y : List Bool, y.length = 24 → (C.wires y).getD a false = y.getD z.val false := by
  intro y yl
  let base := List.replicate 24 false
  have mono := fun g hg => (hm g hg).1
  cases flag : y.getD z.val false with
  | true =>
    have eq := masked_joint_rigidity C.gates w w w y rfl rfl (yl.trans len.symm) mono
      (fun k hk _ => hk.trans (((singleton k).mp hk) ▸ flag.symm)) a hit hit
    exact eq.symm.trans hit
  | false =>
    have eq := masked_joint_rigidity C.gates w w base y rfl (by simp [base,len]) (yl.trans len.symm) mono
      (fun k hk _ => by
        rw [(singleton k).mp hk,flag]
        simp only [base,List.getD_eq_getElem?_getD,List.getElem?_replicate,ite_eq_left z.isLt,Option.getD_some]) a hit hit
    exact eq.symm.trans cold

theorem minimal_crown_first_singleton_raw (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (mini : crownSizeMinimal C) (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (w : List Bool) (len : w.length = 24) (z : Fin 24)
    (singleton : ∀ t, w.getD t false = true ↔ t = z.val)
    (k a : ℕ) (on : (trueOrFlags C.gates w).getD k false = true)
    (before : ∀ j < k, (trueOrFlags C.gates w).getD j false = false)
    (read : a ∈ readAt C.gates 24 k) (hot : (C.wires w).getD a false = true) :
    a = z.val := by
  let base := List.replicate 24 false
  have count := crown_allzero_no_or C hm rep size ors
  have zero (j : ℕ) : (trueOrFlags C.gates base).getD j false = false := by
    have h : true ∉ trueOrFlags C.gates base := List.count_eq_zero.mp count
    cases val : (trueOrFlags C.gates base).getD j false with
    | false => rfl
    | true =>
      by_cases valid : j < (trueOrFlags C.gates base).length
      · have hh : (trueOrFlags C.gates base)[j] = true := by
          simpa [List.getD_eq_getElem?_getD,valid] using val
        exact False.elim (h (hh ▸ List.getElem_mem valid))
      · rw [getD_missing (by omega)] at val
        contradiction
  obtain ⟨hi,co⟩ := first_parent_masked C.gates w base (by simp [len,base]) k on before zero a (len ▸ read) hot
  by_cases small : a < 24
  · exact (singleton a).mp ((val_input (C := C) len small).symm.trans hot)
  have valid : a < 24+C.gates.length := by
    by_contra! no
    have off := val_ge (C := C) len no
    change (C.wires w).getD a false = false at off
    simp_all
  let r := a-24
  have ar : 24+r = a := by dsimp [r]; omega
  have hr : r < C.gates.length := by omega
  have copyEq := masked_singleton_is_raw C hm a w len z singleton hi co
  exact False.elim (minimal_crown_no_raw_copy C hm rep mini ors r z.val hr z.isLt
    (fun u v => ar ▸ copyEq _ (by simp [oneEach])))

end PEqualNP.Research.MissingCell
