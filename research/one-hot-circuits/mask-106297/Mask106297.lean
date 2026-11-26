import PhysicalCornerLower

namespace Mask106297
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def matrix (u : Fin 4) (v : Fin 5) : Bool :=
  (106297 : ℕ).testBit (5 * u.val + v.val)

theorem charged_nine : OnePerShore.charged matrix = 9 := by decide +kernel

theorem lower {s : ℕ} (h : RepSizeAtMost matrix s) : 9 ≤ s := by
  rw [← charged_nine]
  exact OnePerShore.physical_corner_lower 2 3 1 2 (by decide) (by decide)
    (by decide) (by decide) ⟨3, by decide⟩ ⟨0, by decide⟩ h

def witness : Circuit := ⟨[
  ⟨.or,[0,1]⟩, ⟨.or,[7,8]⟩, ⟨.and,[9,10]⟩,
  ⟨.or,[2,3]⟩, ⟨.and,[12,5]⟩, ⟨.and,[2,6]⟩,
  ⟨.or,[4,11]⟩, ⟨.or,[15,13]⟩, ⟨.or,[16,14]⟩], 17⟩

theorem upper : RepSizeAtMost matrix 9 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Monotone2, witness]
  · decide
  · decide +kernel
end Mask106297

theorem PEqualNP.Outside.L_meta_20960 : ¬ (PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 5) => (106297 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  intro h
  have := Mask106297.lower (s := 8) h
  omega
