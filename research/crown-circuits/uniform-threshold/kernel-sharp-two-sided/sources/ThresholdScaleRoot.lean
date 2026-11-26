import ThresholdSharpGrowth
import Mathlib.Topology.Order.IntermediateValue

namespace ThresholdScaleRoot

/-- A positive scale for integer-power estimates, with a caller-supplied lower cutoff. -/
theorem exists_above {k : Nat} (hk : k ≠ 0) {b t : ℝ} (hb : 1 ≤ b) (hbt : b ^ k ≤ t) :
    ∃ x : ℝ, b ≤ x ∧ x ^ k = t := by
  have bt := (le_self_pow₀ hb hk).trans hbt
  have top := le_self_pow₀ (hb.trans bt) hk
  have cnt : ContinuousOn (fun x : ℝ => x ^ k) (Set.Icc b t) :=
    (continuous_id.pow k).continuousOn
  obtain ⟨x, hx, eq⟩ := intermediate_value_Icc bt cnt (show t ∈ Set.Icc (b^k) (t^k) from ⟨hbt, top⟩)
  exact ⟨x, hx.1, eq⟩

#print axioms exists_above
end ThresholdScaleRoot
