import PhysicalCornerLower

namespace Mask28121121
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def matrix (u : Fin 5) (v : Fin 5) : Bool :=
  (28121121 : ℕ).testBit (5 * u.val + v.val)

theorem charged_ten : OnePerShore.charged matrix = 10 := by decide +kernel

theorem lower {s : ℕ} (h : RepSizeAtMost matrix s) : 10 ≤ s := by
  rw [← charged_ten]
  exact OnePerShore.physical_corner_lower 2 3 1 2 (by decide) (by decide)
    (by decide) (by decide) ⟨0, by decide⟩ ⟨0, by decide⟩ h

def witness : Circuit := ⟨[
  ⟨.or,[0,1]⟩,
  ⟨.and,[10,5]⟩,
  ⟨.or,[6,7]⟩,
  ⟨.and,[2,12]⟩,
  ⟨.or,[3,4]⟩,
  ⟨.or,[8,9]⟩,
  ⟨.or,[6,15]⟩,
  ⟨.and,[14,16]⟩,
  ⟨.or,[11,13]⟩,
  ⟨.or,[18,17]⟩], 19⟩

theorem upper : RepSizeAtMost matrix 10 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Monotone2, witness]
  · decide
  · decide +kernel
end Mask28121121

theorem PEqualNP.Outside.L_meta_21246 : ¬ (PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 5) (v : Fin 5) => (28121121 : ℕ).testBit (5 * u.val + v.val)) 9) := by
  intro h
  have := Mask28121121.lower h
  omega
