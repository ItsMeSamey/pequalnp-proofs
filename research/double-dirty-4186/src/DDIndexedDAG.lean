import DDIndexedRows
import DDVirtualDAG

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double
attribute [local instance] gateOpDecEq

def originalSource : Indexed.Ref → Option ℕ
  | some (.gate j, _) => some j
  | _ => none

/-- The virtual DAG uses original IDs only for retained AND gates, including unaffected
clean AND roots; suppressed rows have no vertex. An affected root is replaced by two
fresh ANDs on the given original arm wire and projected guard wire. -/
def indexed (n : ℕ) (C : Circuit) (p : Cuts) (external : Finset ℕ)
    (arms : Fin 2 → ℕ) (guard : ℕ) : DAG where
  paidRows := (Finset.range C.gates.length).filter fun j =>
    (Indexed.ins n C p j).isSome = true ∧ (gateAt C j).op = .and
  extTops := external
  pins j b := originalSource (Indexed.pin (Indexed.build n C p j) n C p j b)
  armPins b pin := Indexed.producer (Indexed.build n C p C.gates.length) (if pin = 0 then arms b else guard)

theorem indexed_reads_row {n g j : ℕ} (C : Circuit) (p : Cuts) (external : Finset ℕ)
    (arms : Fin 2 → ℕ) (guard : ℕ) :
    Node.row j ∈ (indexed n C p external arms guard).readers g ↔
      j < C.gates.length ∧ ((Indexed.ins n C p j).isSome = true ∧ (gateAt C j).op = .and) ∧
        ∃ b : Fin 2, originalSource (Indexed.pin (Indexed.build n C p j) n C p j b) = some g := by
  simp [DAG.readers,indexed,and_assoc]

theorem indexed_reads_arm {n g : ℕ} (C : Circuit) (p : Cuts) (external : Finset ℕ)
    (arms : Fin 2 → ℕ) (guard : ℕ) (b : Fin 2) :
    Node.arm b ∈ (indexed n C p external arms guard).readers g ↔
      ∃ k : Fin 2, Indexed.producer (Indexed.build n C p C.gates.length)
        (if k = 0 then arms b else guard) = some g := by
  simp [DAG.readers,indexed]

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
