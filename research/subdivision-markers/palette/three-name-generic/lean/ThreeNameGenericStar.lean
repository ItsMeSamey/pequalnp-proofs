import ThreeNameGenericHost
namespace ThreeNameGenericStar
open ThreeNamePacked ThreeNameGenericTrail ThreeNamePinReduction

def rawDigest : String := "f675daaacb82285d16389a42a683b69f56b894a5361fc523fa6ba13d5bef585e"
def raw (i : Fin 3) : BitVec 4 := ([8,10,3] : List (BitVec 4)).getD i.val 0
def pins : List (Fin 3) := [0]
def tab : ThreeNamePackedPins.Table 4 := [(3,8)]
def support (_ : Fin 4) : List (Fin 3) := [0]
def words (i : Fin 8) : BitVec 4 := ([2,4,7,6,3,5,2,3] : List (BitVec 4)).getD i.val 0
def frame : Frame (Fin 8) 4 := ⟨Finset.univ, words⟩
def lift : Fin 3 ↪ Fin 8 := ⟨fun i => ⟨i.val+5, by omega⟩, by
  intro a b eq
  have h := congrArg Fin.val eq
  apply Fin.ext
  change a.val+5 = b.val+5 at h
  omega⟩

def terminal : Terminal frame 0 1 2 4 where
  incidence := fun i => ([3,5,9,6,12,10,3,12] : List (BitVec 4)).getD i.val 0
  l := fun i => ([0,0,0,1,2,1,0,2] : List (Fin 4)).getD i.val 0
  r := fun i => ([1,2,3,2,3,3,1,3] : List (Fin 4)).getD i.val 0
  center := 0
  forwardRows := fun i => ([7,3,5,1] : List (BitVec 4)).getD i.val 0
  reverseRows := fun i => ([7,5,3,0] : List (BitVec 4)).getD i.val 0
  graphOK := by decide
  kernelOK := by decide
  starOK := by decide

theorem no (A : Finset (Fin 3)) (hp : pins.toFinset ⊆ A) :
    ¬ Exact (fun i => decode (raw i)) (ThreeNameGenericPositive.named (1 : BitVec 4) 2 4) A :=
  ThreeNameGenericHost.rejects raw pins 1 2 4 tab support (by decide)
    frame frame 0 1 2 lift (by decide) (by decide) (.nil frame) terminal A hp

#print axioms no
end ThreeNameGenericStar
