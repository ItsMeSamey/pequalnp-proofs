import PhysicalCornerLower

namespace Mask810559
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def matrix (u : Fin 4) (v : Fin 6) : Bool :=
  (810559 : ℕ).testBit (6 * u.val + v.val)

theorem charged_ten : OnePerShore.charged matrix = 10 := by decide +kernel

theorem lower {s : ℕ} (h : RepSizeAtMost matrix s) : 10 ≤ s := by
  rw [← charged_ten]
  exact OnePerShore.physical_corner_lower 2 3 0 2 (by decide) (by decide)
    (by decide) (by decide) ⟨1, by decide⟩ ⟨1, by decide⟩ h

def witness : Circuit := ⟨[
  ⟨.or,[7,8]⟩, ⟨.or,[10,9]⟩, ⟨.and,[1,11]⟩,
  ⟨.or,[4,6]⟩, ⟨.and,[2,13]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,15]⟩,
  ⟨.or,[0,12]⟩, ⟨.or,[17,14]⟩, ⟨.or,[18,16]⟩], 19⟩

theorem upper : RepSizeAtMost matrix 10 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Monotone2, witness]
  · decide
  · decide +kernel
end Mask810559

theorem PEqualNP.Outside.L_meta_23331 : ¬ (PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 6) => (810559 : ℕ).testBit (6 * u.val + v.val)) 9) := by
  intro h
  have := Mask810559.lower h
  omega
