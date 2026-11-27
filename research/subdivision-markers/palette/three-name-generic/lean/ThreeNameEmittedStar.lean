import ThreeNameGenericHost
namespace ThreeNameEmittedStar
open ThreeNamePacked ThreeNameGenericTrail ThreeNamePinReduction
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def rawDigest : String := "f675daaacb82285d16389a42a683b69f56b894a5361fc523fa6ba13d5bef585e"
abbrev O := Fin 3
abbrev J := Fin 9
def raw (i : O) : BitVec 4 := ([8, 10, 3] : List (BitVec 4)).getD i.val 0
def pins : List O := [0]
def pivots : ThreeNamePackedPins.Table 4 := [(3, 8)]
def supports (j : Fin 4) : List O := match j.val with
  | 3 => [0]
  | _ => []
def words (i : J) : BitVec 4 := ([2, 4, 7, 6, 3, 5, 2, 3] : List (BitVec 4)).getD i.val 0
def attach (i : O) : J := ([8, 6, 7] : List (J)).getD i.val 0
def lift : O ↪ J := ⟨attach, by decide⟩
def p0 : Frame J 4 := ⟨([0, 1, 2, 3, 4, 5, 6, 7] : List (J)).toFinset,words⟩
def trail : Trail ({0,1,2} : Finset J) p0 p0 := .nil p0
def l (i : J) : Fin 4 := ([0, 0, 0, 1, 2, 1, 0, 2, 0] : List (Fin 4)).getD i.val 0
def r (i : J) : Fin 4 := ([1, 2, 3, 2, 3, 3, 1, 3, 0] : List (Fin 4)).getD i.val 0
def inc (i : J) : BitVec 4 := ([3, 5, 9, 6, 12, 10, 3, 12, 0] : List (BitVec 4)).getD i.val 0
def fwd (i : Fin 4) : BitVec 4 := ([7, 3, 5, 1] : List (BitVec 4)).getD i.val 0
def back (i : Fin 4) : BitVec 4 := ([8, 10, 12, 0] : List (BitVec 4)).getD i.val 0
def terminal : Terminal p0 0 1 2 4 :=
  ⟨inc,l,r,0,fwd,back,by decide,by decide,by decide⟩
theorem no (A : Finset O) (hp : pins.toFinset ⊆ A) :
    ¬ Exact (fun i => decode (raw i)) (ThreeNameGenericPositive.named (1 : BitVec 4) 2 4) A :=
  ThreeNameGenericHost.rejects raw pins 1 2 4 pivots supports (by decide)
    p0 p0 0 1 2 lift (by decide) (by decide) trail terminal A hp
#print axioms no
end ThreeNameEmittedStar
