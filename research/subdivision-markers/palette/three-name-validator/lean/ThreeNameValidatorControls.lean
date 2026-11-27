import ThreeNameValidator
import ThreeNameEmittedSplit
namespace ThreeNameValidatorControls
open ThreeNameValidator ThreeNameCheckTrail
open ThreeNameEmittedSplit21124e661929
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def data : Input 4 5 := ⟨raw,pins,1,2,4⟩
def next : RawJump J 5 := ⟨p1,p1.ground,m0,{0}⟩
def graph : RawTerminal J 5 4 := ⟨inc,l,r,0,fwd,back⟩
def payload : Star 4 5 := ⟨10,4,pivots,supports,p0,0,1,2,attach,[next],graph⟩
def graphInput : Certificate 4 5 := .star payload

theorem good : validate data graphInput = true := by decide
theorem original_no : ¬ ExistsExact data := fun h => (by
  have wrong := (sound data graphInput good).mp h
  contradiction)

def tiny : Input 1 3 := ⟨fun _ => 1,[],1,2,4⟩
theorem yes : validate tiny (.positive [0] [0] [1] [2]) = true := by decide
theorem bad_positive : validate tiny (.positive [] [0] [1] [2]) = false := by decide
theorem bad_conflict : validate tiny (.conflict false false true [0]) = false := by decide
theorem bad_outside : validate tiny (.outside [0]) = false := by decide
def dupPayload : Star 4 5 := ⟨10,4,pivots,supports,p0,0,1,2,fun _ => 0,[next],graph⟩
theorem bad_attach : validate data (.star dupPayload) = false := by decide
theorem bad_pins : validate data (.star {payload with supports := fun _ => []}) = false := by decide
theorem bad_jump : validate data (.star {payload with jumps := [{next with retained := ∅}]}) = false := by decide
#print axioms good
#print axioms original_no
end ThreeNameValidatorControls
