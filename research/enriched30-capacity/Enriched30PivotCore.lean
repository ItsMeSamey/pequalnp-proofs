import Enriched30Data
import Mathlib.Data.List.GetD

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Enriched30Pivot
open PEqualNP.CircuitLowerBounds

abbrev Cell := Fin 1024
abbrev bank := Enriched30Data.bank
abbrev label : Cell → Bool := Enriched30Data.target

def raw (c : Cell) : List Bool :=
  (List.range 64).map fun i => decide (i = c.val / 32 ∨ i = 32 + c.val % 32)

def bits (c : Cell) : List Bool :=
  let values := Enriched30Data.circuit.wires (raw c)
  bank.map fun w => values.getD w false

theorem raw_length (c : Cell) : (raw c).length = 64 := by simp [raw]

theorem bits_length (c : Cell) : (bits c).length = 30 := by
  have h : bank.length = 30 := by decide
  simpa [bits] using h

/-- This lookup is definitionally the repository circuit evaluated at the named output. -/
theorem bits_eq_actual_outputs (c : Cell) :
    bits c = bank.map (fun w => ({Enriched30Data.circuit with output := w} : Circuit).eval (raw c)) := by
  rfl

def mandatory : Finset Nat :=
  (Finset.range 30).filter fun i => bank[i]? ≠ some 90 ∧ bank[i]? ≠ some 137

def mandatoryWires : Finset Nat := mandatory.image (fun i => bank.getD i 0)

theorem mandatory_card : mandatory.card = 28 := by decide

theorem mandatory_lt {j : Nat} (hj : j ∈ mandatory) : j < 30 :=
  Finset.mem_range.mp (Finset.mem_filter.mp hj).1

def cell (n : Nat) : Cell := ⟨n % 1024, Nat.mod_lt _ (by decide)⟩

def essentialPair (j : Nat) : Cell × Cell :=
  let e := (Enriched30Data.essential.find? (fun e => e.1 == bank.getD j 0)).getD (0,0,0)
  (cell e.2.1,cell e.2.2)

def binatePairs (j : Nat) : (Cell × Cell) × (Cell × Cell) :=
  let e := (Enriched30Data.binate.find? (fun e => e.1 == bank.getD j 0)).getD (0,0,0,0,0)
  ((cell e.2.1,cell e.2.2.1),(cell e.2.2.2.1,cell e.2.2.2.2))

def binate : Finset Nat := (Finset.range 30).filter fun j =>
  (Enriched30Data.binate.map Prod.fst).contains (bank.getD j 0)

theorem binate_card : binate.card = 11 := by decide

/-- Finite checking computes physical wire lists once per cell and compares every slot. -/
def edgeCode (j : Nat) (a b : Cell) : Bool :=
  let lo := bits a
  let hi := bits b
  !lo.getD j false && hi.getD j false &&
    (List.range 30).all (fun i => i == j || lo.getD i false == hi.getD i false)

def Edge (j : Nat) (a b : Cell) : Prop :=
  (bits a).getD j false = false ∧ (bits b).getD j false = true ∧
    ∀ k : Nat, k ≠ j → (bits a).getD k false = (bits b).getD k false

theorem edge_sound {j : Nat} {a b : Cell} (h : edgeCode j a b = true) : Edge j a b := by
  simp only [edgeCode, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨lo,hi⟩,rest⟩ := h
  refine ⟨lo,hi,?_⟩
  intro k hk
  by_cases lt : k < 30
  · have eq := List.all_eq_true.mp rest k (List.mem_range.mpr lt)
    simpa [hk] using eq
  · rw [List.getD_eq_default _ _ (by simpa [bits_length] using Nat.le_of_not_gt lt),
        List.getD_eq_default _ _ (by simpa [bits_length] using Nat.le_of_not_gt lt)]

def essentialCheck (j : Fin 30) : Bool :=
  let p := essentialPair j.val
  (label p.1 != label p.2) && edgeCode j.val p.1 p.2

def binateCheck (j : Fin 30) : Bool :=
  let r := (binatePairs j.val).1
  let f := (binatePairs j.val).2
  (!label r.1 && label r.2 && label f.1 && !label f.2) &&
    (edgeCode j.val r.1 r.2 && edgeCode j.val f.1 f.2)

end Enriched30Pivot
