import NativeSelector
import NativeTable

namespace ThresholdStarWindow
open Research.Graph9822Resolution

/-- A gate list separating the original signed rows pays at least seven physical ANDs.
The raw bank may expand each input to an arbitrary OR of singleton-point and tag flags. -/
theorem native_seven_ands (gs : List Gate) (start out : Nat) (raw : Nat → List Nat) (bias : Wire)
    (pos : ∀ r, positiveRow r = true → eval gs start (bankWire raw bias (nativeMask r)) out = true)
    (neg : ∀ r, negativeRow r = true → eval gs start (bankWire raw bias (nativeMask r)) out = false) :
    7 ≤ andCount gs := by
  have capacity : 69 ≤ 2 ^ andCount gs := by
    apply selector_capacity gs start out raw bias (fun j : Fin 69 => (bad j).2)
    · intro j
      obtain ⟨hr, hm⟩ := badRows_native j
      rw [← hm]
      exact neg _ hr
    · intro j k h
      obtain ⟨r, hr, hits⟩ := List.any_eq_true.mp (native_clashes j k h)
      have valid := List.all_eq_true.mp goodRows_native r hr
      simp only [goodCheck, Bool.and_eq_true, beq_iff_eq] at valid
      refine ⟨r.2, by simpa using hits, ?_⟩
      rw [← valid.2]
      exact pos _ valid.1
  by_contra h
  have small : andCount gs ≤ 6 := by omega
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) small
  change 2 ^ andCount gs ≤ 64 at bound
  omega

end ThresholdStarWindow

#print axioms ThresholdStarWindow.native_clashes
#print axioms ThresholdStarWindow.native_seven_ands
