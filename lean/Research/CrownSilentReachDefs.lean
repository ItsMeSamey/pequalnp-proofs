import Research.CrownRawCharge
namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def rawSupport (C : Circuit) (a : ℕ) : Finset (Fin 24) :=
  Finset.univ.filter (fun t => (C.wires (singleInput t)).getD a false)

def silentIncident (C : Circuit) (r : Fin 24) (k : Fin C.gates.length) : Bool :=
  decide (r ∈ rawSupport C (operand C k 0) ∨ r ∈ rawSupport C (operand C k 1))

def silentBoth (C : Circuit) (R : Finset (Fin 24)) (k : Fin C.gates.length) : Bool :=
  decide ((∃ r∈R,r∈rawSupport C (operand C k 0)) ∧ (∃ r∈R,r∈rawSupport C (operand C k 1)))

def silentGates (C : Circuit) (R : Finset (Fin 24)) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun k => chargeable C k = true ∧ ∃ r∈R,silentIncident C r k=true)

theorem chargeable_cold (C : Circuit) (k : Fin C.gates.length) (ok : chargeable C k = true) :
    (C.wires (List.replicate 24 false)).getD (operand C k 0) false = false ∧
    (C.wires (List.replicate 24 false)).getD (operand C k 1) false = false := by
  unfold chargeable at ok
  have h := Bool.and_eq_true_iff.mp ok
  exact ⟨by simpa using (Bool.and_eq_true_iff.mp h.1).2, by simpa using h.2⟩
end PEqualNP.Research.MissingCell
