import ThreeNameGenericTrail

namespace ThreeNameCheckTrail
open ThreeNamePacked ThreeNameGenericTrail

/-- Raw jump data, including the proposed next frame. No validity fields. -/
structure RawJump (J : Type) (w : Nat) where
  next : Frame J w
  retained : Finset J
  rows : Fin w → BitVec w
  interface : Finset (BitVec w)

structure RawTerminal (J : Type) (w h : Nat) where
  incidence : J → BitVec h
  l : J → Fin h
  r : J → Fin h
  center : Fin h
  forwardRows : Fin h → BitVec w
  reverseRows : Fin w → BitVec h

variable {J : Type} [DecidableEq J] {w h : Nat}

def jump (roots : Finset J) (p : Frame J w) (raw : RawJump J w) :
    Option (Jump roots p raw.next) :=
  if ok : ThreeNameProjectionStep.checkTable roots raw.retained p.carrier raw.next.carrier
      (rowHom raw.rows) (raw.interface.image decode) = true then
    some ⟨raw.retained,raw.rows,raw.interface,ok⟩
  else none

/-- The typed tail starts at the exact frame validated by the preceding jump. -/
def replay (roots : Finset J) (start : Frame J w) :
    List (RawJump J w) → Option (Σ last : Frame J w, Trail roots start last)
  | [] => some ⟨start,.nil start⟩
  | raw :: rest => do
      let first ← jump roots start raw
      let ⟨last, tail⟩ ← replay roots raw.next rest
      pure ⟨last,.cons first tail⟩

def terminal (p : Frame J w) (a b c : J) (raw : RawTerminal J w h) :
    Option (Terminal p a b c h) :=
  if graphOK : ThreeNamePackedExample.endpointCheck p.ground raw.incidence raw.l raw.r = true then
    if kernelOK : checkKernel p.ground p.words raw.incidence raw.forwardRows raw.reverseRows = true then
      if starOK : decide ((raw.l a = raw.center ∨ raw.r a = raw.center) ∧
          (raw.l b = raw.center ∨ raw.r b = raw.center) ∧
          (raw.l c = raw.center ∨ raw.r c = raw.center)) = true then
        some ⟨raw.incidence,raw.l,raw.r,raw.center,raw.forwardRows,raw.reverseRows,
          graphOK,kernelOK,starOK⟩
      else none
    else none
  else none

/-- An accepted return contains the path and terminal certificate required by the host. -/
def check (roots : Finset J) (start : Frame J w) (jumps : List (RawJump J w))
    (a b c : J) (raw : RawTerminal J w h) :
    Option (Σ last : Frame J w, Trail roots start last × Terminal last a b c h) := do
  let ⟨last, trail⟩ ← replay roots start jumps
  let term ← terminal last a b c raw
  pure ⟨last,trail,term⟩

end ThreeNameCheckTrail
