import ThreeNameDense
namespace ThreeNameDenseControls
open ThreeNameDense
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def physical : DenseInput := ⟨4,5,[8,10,3,16],[0],[1,2,4]⟩
def initial : DenseFrame := ⟨[0,1,2,3,4,5,6,7,8],[2,4,7,6,3,5,2,3,16,0]⟩
def reduced : DenseFrame := {initial with ground := [0,1,2,3,4,5,6,7]}
def jump : DenseJump := ⟨reduced,reduced.ground,[1,2,4,0,0],[0]⟩
def graph : DenseGraph :=
  ⟨[3,5,9,6,12,10,3,12,0,0],[0,0,0,1,2,1,0,2,0,0],
   [1,2,3,2,3,3,1,3,0,0],0,[7,3,5,1],[8,10,12,0,0]⟩
def star : DenseStar :=
  ⟨10,4,[(3,8)],[[],[],[],[0],[]],initial,[0,1,2],[9,6,7,8],[jump],graph⟩
def tiny : DenseInput := ⟨1,3,[1],[],[1,2,4]⟩
def yes : DenseCertificate := .positive [0] [0] [1] [2]

def suite : List (String × Option Bool × Option Bool) :=
  [("valid split",check physical (.star star),some false),
   ("valid positive",check tiny yes,some true),
   ("valid outside",check {tiny with columns := [2]} (.outside [0]),some false),
   ("valid pin conflict",check {tiny with columns := [2], pins := [0]} (.conflict true false false [0]),some false),
   ("negative word",check {tiny with columns := [-1]} yes,none),
   ("oversized word",check {tiny with columns := [9]} yes,none),
   ("dependent names",check {tiny with names := [1,2,3]} yes,none),
   ("negative ID",check tiny (.positive [-1] [0] [1] [2]),none),
   ("missing ID",check tiny (.positive [0] [1] [1] [2]),none),
   ("invalid parity",check tiny (.positive [0] [0] [0] [2]),none),
   ("repeated roots",check physical (.star {star with roots := [1,1,2]}),none),
   ("bad attachment",check physical (.star {star with attach := [9,6,7,7]}),none),
   ("short table",check physical (.star {star with graph := {graph with reverseRows := [8,10,12,0]}}),none),
   ("bad transition",check physical (.star {star with jumps := [{jump with retained := []}]}),none),
   ("wrong incidence",check physical (.star {star with graph := {graph with center := 3}}),none)]

def run : IO Unit := do
  for (label,actual,expected) in suite do
    unless actual == expected do throw (IO.userError s!"{label}: got {actual}, expected {expected}")
    IO.println s!"{label}: {actual}"
end ThreeNameDenseControls

def main : IO Unit := ThreeNameDenseControls.run
