import ThresholdSharedFlow
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

namespace ThresholdLeakPins

open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ResidualSurplus
open ThresholdSharedFlow

variable {C : Circuit} {n : Nat} (L : Layout C n)

/-- A physical operand occurrence. False denotes left, true denotes right. -/
abbrev Pin (C : Circuit) := Id C × Bool

def source (p : Pin C) : Nat := if p.2 then L.right p.1 else L.left p.1

def opposite (p : Pin C) : Pin C := (p.1, !p.2)

@[simp] theorem opposite_opposite (p : Pin C) : opposite (opposite p) = p := by
  rcases p with ⟨i, b⟩
  cases b <;> rfl

def leaking (U : Id C) (p : Pin C) : Prop :=
  L.op p.1 = .and ∧ active L U p.1 = false ∧ on L U (source L p) = true

noncomputable def leakPins (U : Id C) : Finset (Pin C) := by
  classical
  exact Finset.univ.filter (leaking L U)

/-- The original numerical flow counts physical occurrences, including both
positions when the wires plugged into them coincide. -/
theorem card_leakPins (U : Id C) : (leakPins L U).card = leak L U := by
  classical
  calc
    _ = ∑ p : Pin C, if leaking L U p then 1 else 0 := by
      simpa only [leakPins, Nat.cast_id] using
        (Finset.sum_boole (R := ℕ) (leaking L U) Finset.univ).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      unfold leak
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      cases hop : L.op i <;> cases ha : active L U i <;>
        cases hl : on L U (L.left i) <;> cases hr : on L U (L.right i) <;>
        simp [leaking, source, inCount, hop, ha, hl, hr]

/-- The reader index alone need not be injective. The opposite physical
occurrence determines the original occurrence, whose one source determines V. -/
theorem opposite_reader_injOn (S : Finset (Id C)) (reader : Id C → Pin C)
    (reads : ∀ v ∈ S, source L (reader v) = n + v.val) :
    (S : Set (Id C)).InjOn (fun v => opposite (reader v)) := by
  intro v hv w hw heq
  have pins : reader v = reader w := by
    simpa only [opposite_opposite] using congrArg opposite heq
  have wires := congrArg (source L) pins
  rw [reads v hv, reads w hw] at wires
  exact Fin.ext (by omega)

/-- Charge the warm partners of cold private outputs to the actual probe leak.
The caller supplies any one occurrence of each private output at its AND
reader; uniqueness need not be reproved for this counting step. -/
theorem warm_private_card_le_leak (U : Id C) (center : L.op U = .or)
    (S : Finset (Id C)) (reader : Id C → Pin C)
    (reads : ∀ v ∈ S, source L (reader v) = n + v.val)
    (andReader : ∀ v ∈ S, L.op (reader v).1 = .and)
    (cold : ∀ v ∈ S, active L U v = false)
    (warm : ∀ v ∈ S, on L U (source L (opposite (reader v))) = true) :
    S.card ≤ leak L U := by
  classical
  rw [← card_leakPins L U]
  apply Finset.card_le_card_of_injOn (fun v => opposite (reader v)) _
    (opposite_reader_injOn L S reader reads)
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, andReader v hv, ?_, warm v hv⟩
  have hne : (reader v).1 ≠ U := by
    intro h
    have bad := andReader v hv
    rw [h, center] at bad
    cases bad
  have off : on L U (source L (reader v)) = false := by
    rw [reads v hv]
    exact cold v hv
  change active L U (reader v).1 = false
  rw [row_eq L U (reader v).1, if_neg hne, andReader v hv]
  cases hside : (reader v).2 <;> simp [source, hside] at off <;> simp [off]

end ThresholdLeakPins
