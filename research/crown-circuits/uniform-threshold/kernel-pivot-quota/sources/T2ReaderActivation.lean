import T2RawIsolation

namespace T2ReaderActivation
open PEqualNP.CircuitLowerBounds ResidualSurplus T2RawIsolation

def absorbing : Op → Bool
  | .and => false
  | .or => true

/-- If a single raw changes the output, its unique binary reader cannot
have an absorbing value on the other operand. This applies to either operand
orientation and to the physical prefix evaluation. -/
theorem other_not_absorbing (pre post : List Gate) (op : Op) (orient : Bool)
    (x p out : Nat) (u v : List Bool)
    (hx : AgreeOff x u v) (ne : p ≠ x) (nout : out ≠ x)
    (preMiss : ∀ row ∈ pre, x ∉ row.inputs)
    (postMiss : ∀ row ∈ post, x ∉ row.inputs)
    (changes : let g := if orient then binary op x p else binary op p x
      Circuit.eval ⟨pre ++ g::post,out⟩ u ≠ Circuit.eval ⟨pre ++ g::post,out⟩ v) :
    (run pre u).getD p false ≠ absorbing op := by
  intro blocked
  have pv := (unread_run pre hx preMiss).2 p ne
  have blocked' := pv.symm.trans blocked
  apply changes
  apply isolated_reader pre post _ hx nout preMiss postMiss
  cases orient <;> cases op <;>
    simp_all [absorbing, val, binary, gateOp, GateOp.eval]

#print axioms other_not_absorbing
end T2ReaderActivation
