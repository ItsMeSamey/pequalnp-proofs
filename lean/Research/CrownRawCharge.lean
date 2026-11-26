import Research.CrownEdgeCharge

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge
private theorem raw_preserved (gs : List Gate) (out : ℕ) (w : List Bool) (a : ℕ) (ha : a<w.length) :
    ((Circuit.mk gs out).wires w).getD a false = w.getD a false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((Circuit.mk gs out).wires (advance g w)).getD a false = _
    rw [ih _ (by rw [advance_len]; omega),getD_advance_lt _ _ _ ha]

theorem raw_single_support {n} (C : Circuit) (t s : Fin n) :
    (C.wires (singleInput s)).getD t.val false = decide (t=s) := by
  rw [raw_preserved C.gates C.output _ _ (by simp [singleInput])]
  simp [singleInput,List.getD_eq_getElem?_getD,t.isLt]

theorem singletonMass_raw (C : Circuit) (t : Fin 24) : singletonMass C t.val = singletonWeight C t := by
  simp only [singletonMass,Finset.sum_filter,raw_single_support,decide_eq_true_eq]; simp

theorem chargeable_capacities (C : Circuit) (hm : Monotone2 C) (k : Fin C.gates.length) (ok : chargeable C k=true) :
    singletonMass C (operand C k 0) ≤ 1 ∧ singletonMass C (operand C k 1) ≤ 1 := by
  unfold chargeable at ok
  have h := Bool.and_eq_true_iff.mp ok
  have p := (Bool.and_eq_true_iff.mp h.1).2
  exact ⟨singleton_weight_capacity C hm _ (by simpa using p), singleton_weight_capacity C hm _ (by simpa using h.2)⟩

theorem raw_left_charge_cap (C : Circuit) (hm : Monotone2 C) (k : Fin C.gates.length)
    (ok : chargeable C k=true) (p : Fin 24) (raw : operand C k 0 = p.val) :
    singletonMass C (operand C k 0) * singletonMass C (operand C k 1) ≤ singletonWeight C p := by
  rw [raw,singletonMass_raw]
  have nn : 0 ≤ singletonWeight C p := by unfold singletonWeight; positivity
  simpa using mul_le_mul_of_nonneg_left (chargeable_capacities C hm k ok).2 nn

theorem raw_right_charge_cap (C : Circuit) (hm : Monotone2 C) (k : Fin C.gates.length)
    (ok : chargeable C k=true) (p : Fin 24) (raw : operand C k 1 = p.val) :
    singletonMass C (operand C k 0) * singletonMass C (operand C k 1) ≤ singletonWeight C p := by
  rw [raw,singletonMass_raw]
  have nn : 0 ≤ singletonWeight C p := by unfold singletonWeight; positivity
  simpa using mul_le_mul_of_nonneg_right (chargeable_capacities C hm k ok).1 nn
theorem chargeable_product_le_one (C : Circuit) (hm : Monotone2 C)
    (k : Fin C.gates.length) (ok : chargeable C k=true) :
    singletonMass C (operand C k 0) * singletonMass C (operand C k 1) ≤ 1 := by
  have caps := chargeable_capacities C hm k ok
  have nn : 0 ≤ singletonMass C (operand C k 1) := by
    apply Finset.sum_nonneg
    intro t _
    unfold singletonWeight
    positivity
  simpa using mul_le_mul caps.1 caps.2 nn (zero_le_one : (0 : ℚ) ≤ 1)

end PEqualNP.Research.MissingCell
