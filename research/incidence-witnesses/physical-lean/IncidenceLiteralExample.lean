import IncidencePinnedCube
namespace IncidenceZeroRestriction.Example
open CircuitRewire
def gates : Nat→Gate
  | 0 => ⟨.join,0,1⟩
  | 1 => ⟨.join,3,1⟩
  | 2 => ⟨.meet,0,2⟩
  | _ => ⟨.join,4,5⟩
def pins (i : Nat) : Option Nat := if i=0 then none else some (i-1)
def result := compileLiteral 3 2 gates pins 4
-- An OR forwarded by the first deletion makes the following OR's two operands equal.
-- The literal compiler retains that row and preserves both of its physical pin occurrences.
example : result.size=1 ∧ result.refs 6=some 2 ∧ (result.code 0).op=.join ∧
    (result.code 0).left=0 ∧ (result.code 0).right=0 := by decide
end IncidenceZeroRestriction.Example
