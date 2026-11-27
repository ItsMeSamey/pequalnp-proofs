import ThreeNameGenericHost
namespace ThreeNameEmittedSplit21124e661929
open ThreeNamePacked ThreeNameGenericTrail ThreeNamePinReduction
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def rawDigest : String := "21124e66192983f961ef8069961cccd21dad15a82e0953b191bcc04d1964ecbb"
abbrev O := Fin 4
abbrev J := Fin 10
def raw (i : O) : BitVec 5 := ([8, 10, 3, 16] : List (BitVec 5)).getD i.val 0
def pins : List O := [0]
def pivots : ThreeNamePackedPins.Table 5 := [(3, 8)]
def supports (j : Fin 5) : List O := match j.val with
  | 3 => [0]
  | _ => []
def words (i : J) : BitVec 5 := ([2, 4, 7, 6, 3, 5, 2, 3, 16] : List (BitVec 5)).getD i.val 0
def attach (i : O) : J := ([9, 6, 7, 8] : List (J)).getD i.val 0
def lift : O ↪ J := ⟨attach, by decide⟩
def p0 : Frame J 5 := ⟨([0, 1, 2, 3, 4, 5, 6, 7, 8] : List (J)).toFinset,words⟩
def p1 : Frame J 5 := ⟨([0, 1, 2, 3, 4, 5, 6, 7] : List (J)).toFinset,words⟩
def m0 (i : Fin 5) : BitVec 5 := ([1, 2, 4, 0, 0] : List (BitVec 5)).getD i.val 0
def j0 : Jump ({0,1,2} : Finset J) p0 p1 := ⟨([0, 1, 2, 3, 4, 5, 6, 7] : List (J)).toFinset,m0,([0] : List (BitVec 5)).toFinset, by decide⟩
def trail : Trail ({0,1,2} : Finset J) p0 p1 := .cons j0 (.nil p1)
def l (i : J) : Fin 4 := ([0, 0, 0, 1, 2, 1, 0, 2, 0, 0] : List (Fin 4)).getD i.val 0
def r (i : J) : Fin 4 := ([1, 2, 3, 2, 3, 3, 1, 3, 0, 0] : List (Fin 4)).getD i.val 0
def inc (i : J) : BitVec 4 := ([3, 5, 9, 6, 12, 10, 3, 12, 0, 0] : List (BitVec 4)).getD i.val 0
def fwd (i : Fin 4) : BitVec 5 := ([7, 3, 5, 1] : List (BitVec 5)).getD i.val 0
def back (i : Fin 5) : BitVec 4 := ([8, 10, 12, 0, 0] : List (BitVec 4)).getD i.val 0
def terminal : Terminal p1 0 1 2 4 :=
  ⟨inc,l,r,0,fwd,back,by decide,by decide,by decide⟩
theorem no (A : Finset O) (hp : pins.toFinset ⊆ A) :
    ¬ Exact (fun i => decode (raw i)) (ThreeNameGenericPositive.named (1 : BitVec 5) 2 4) A :=
  ThreeNameGenericHost.rejects raw pins 1 2 4 pivots supports (by decide)
    p0 p1 0 1 2 lift (by decide) (by decide) trail terminal A hp
#print axioms no
end ThreeNameEmittedSplit21124e661929
