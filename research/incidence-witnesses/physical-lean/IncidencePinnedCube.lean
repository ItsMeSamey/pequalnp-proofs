import IncidenceDenseRestriction
namespace IncidenceZeroRestriction
open CircuitRewire
abbrev Cube := Nat→Bool
def liftInputs (init : Nat→Option Nat) (z : Cube) (i : Nat) : Bool :=
  (init i).elim false z
def coordinate (i : Nat) : Set Cube := {z|z i=true}

theorem all_masks (m n s o : Nat) (raw : Nat→Gate) (init : Nat→Option Nat)
    (X : Nat→Set Cube) (bound : ∀ i<m,Below n (init i))
    (inputs : ∀ i<m,X i=coordinate i) (order : ∀ j<s,OrderedBinary (raw j) (m+j))
    (sem : ∀ i<s,X (m+i)=(raw i).eval X) (out : o<m+s)
    (present : ∃ z,liftInputs init z∈X o) :
    let p := compileLiteral m n raw init s
    let low := fun i=>liftInputs init ⁻¹' X i
    p.size+charged raw (zeroAt low (fun _=>true)) s=s ∧
    (∀ i<p.size,OrderedBinary (p.code i) (n+i)) ∧
    ∃ j<n+p.size,p.refs o=some j ∧ ∃ Y : Nat→Set Cube,(∀ i<n,Y i=coordinate i) ∧
      (∀ a<p.size,Y (n+a)=(p.code a).eval Y) ∧ ∀ z,z∈Y j ↔ liftInputs init z∈X o := by
  let low := fun i=>liftInputs init ⁻¹' X i
  have inlaw (i : Nat) (hi : i<m) : low i=CircuitRewire.read coordinate (init i) := by
    ext z
    cases e : init i <;> simp [low,inputs i hi,coordinate,liftInputs,CircuitRewire.read,e]
  have gate (i : Nat) (hi : i<s) : low (m+i)=(raw i).eval low := by
    change _ ⁻¹' X (m+i) = _
    rw [sem i hi,preimage_gate]
  obtain ⟨count,ord,j,hj,wire,Y,initial,ev,eq⟩ :=
    dense_minor m n s o raw init low coordinate (fun _=>true) bound inlaw
      (fun _ _=>rfl) order gate out present
  exact ⟨count,ord,j,hj,wire,Y,initial,ev,fun z=>by rw [eq]; rfl⟩
#print axioms all_masks
end IncidenceZeroRestriction
