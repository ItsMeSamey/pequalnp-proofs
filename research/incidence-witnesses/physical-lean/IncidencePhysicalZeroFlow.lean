import IncidenceZeroRestriction
import IncidenceOperandLedger
namespace IncidenceZeroRestriction
open CircuitRewire
open IncidenceOperandLedger (removed bit fan oneAnd)
open scoped BigOperators
theorem charged_int (raw : Nat→Gate) (z : Nat→Bool) (s : Nat) :
    (charged raw z s : Int)=∑ j∈Finset.range s,removed z (raw j) := by
  induction s with
  | zero => simp [charged]
  | succ j ih =>
    rw [charged_succ,Finset.sum_range_succ,Nat.cast_add,ih]
    unfold removed bit lost
    cases h : z (raw j).left || z (raw j).right <;> simp [h]

/-- The physical number of rows removed by literal compilation equals the raw/fanout/AND
flow. No liveness or sole-reader compensation premise is used in the equality. -/
theorem savings (m n s : Nat) (raw : Nat→Gate) (init : Nat→Option Nat)
    (z : Nat→Bool) (inputs : ∀ i<m,(init i).isNone=z i)
    (order : ∀ i<s,OrderedBinary (raw i) (m+i))
    (gate : ∀ i<s,z (m+i)=deadOut (raw i).op (z (raw i).left) (z (raw i).right)) :
    (s : Int)-(compileLiteral m n raw init s).size =
      (∑ w∈Finset.range m,fan raw s w * bit (z w)) +
      (∑ i∈Finset.range s,(fan raw s (m+i)-1)*bit (z (m+i))) +
      ∑ i∈Finset.range s,oneAnd z (raw i) := by
  have size := (literal_counts m n s raw init z inputs order gate).2
  have count : (s : Int)-(compileLiteral m n raw init s).size=(charged raw z s : Int) := by omega
  rw [count,charged_int]
  apply IncidenceOperandLedger.literal_ledger
  · intro i hi
    have a := (order i hi).1
    have b := (order i hi).2.1
    exact ⟨by omega,by omega⟩
  · exact fun i hi=>(order i hi).2.2
  · intro i hi
    rw [gate i hi]
    cases h : (raw i).op <;> simp [deadOut,IncidenceOperandLedger.zeroAt,h]
#print axioms savings
end IncidenceZeroRestriction
