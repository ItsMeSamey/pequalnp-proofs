import ThreeNamePackedSteps01
namespace ThreeNamePackedExample
open ThreeNamePacked ThreeNameChain ThreeNameSplitCircuit
open scoped BigOperators
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def x2 : Finset I := ([0, 1, 2, 3, 4, 5, 7, 14] : List (I)).toFinset
def rows2 (i : Fin 7) : BitVec 7 := ([1, 0, 4, 8, 0, 0, 0] : List (BitVec 7)).getD i.val 0
def tab2 : Finset (BitVec 7) := ([0, 4, 8, 12] : List (BitVec 7)).toFinset
def step2 : Step roots p2 p3 :=
  diagonalStep words g2 g3 roots x2 13 tab2 (by decide)
def path : Path roots p0 p3 := .cons step0 (.cons step1 (.cons step2 (.nil p3)))
end ThreeNamePackedExample
