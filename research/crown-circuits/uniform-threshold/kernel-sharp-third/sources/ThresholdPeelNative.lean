import ThresholdPinCompiler
import ThresholdRemoteAnchor

open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdPinCompiler
namespace ThresholdPeelNative

theorem witness_minor {m : Nat} (C : Circuit) (p : Fin m)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (w : ThresholdRemoteAnchor.Witness (fun a => C.eval (List.ofFn a)) p) :
    let D := restrictFalse C m p.val
    PEqualNP.MetaComplexity.Monotone2 D ∧
    (∀ v : List Bool, v.length=m → D.eval v=C.eval (pinFalse v p.val)) ∧
    ors D.gates+1≤ors C.gates := by
  obtain ⟨⟨x, _, flip⟩, z, off, pos⟩ := w
  apply essential_pin_false C p mono x (ThresholdRemoteAnchor.setBit x p true) z _ flip off pos
  intro i hi
  simp [ThresholdRemoteAnchor.setBit,hi]

#print axioms witness_minor
end ThresholdPeelNative
