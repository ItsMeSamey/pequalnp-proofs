import ThreeNameProjectionStep
import ThreeNamePackedTerminal
namespace ThreeNameGenericTrail
open ThreeNamePacked ThreeNameChain
open scoped BigOperators

structure Frame (J : Type) (w : Nat) where
  ground : Finset J
  words : J → BitVec w

def Frame.carrier {J w} (fr : Frame J w) : Carrier J (Vec w) :=
  ⟨fr.ground,fun i => decode (fr.words i)⟩

variable {J : Type} [DecidableEq J] {w : Nat}

structure Jump (roots : Finset J) (p q : Frame J w) where
  retained : Finset J
  rows : Fin w → BitVec w
  interface : Finset (BitVec w)
  accepts : ThreeNameProjectionStep.checkTable roots retained p.carrier q.carrier
    (rowHom rows) (interface.image decode) = true

def Jump.step {R : Finset J} {p q : Frame J w} (j : Jump R p q) :
    Step R p.carrier q.carrier :=
  ThreeNameProjectionStep.checkedStep R j.retained _ _ _ _ j.accepts

inductive Trail (roots : Finset J) : Frame J w → Frame J w → Type
  | nil (p) : Trail roots p p
  | cons {p q z} (head : Jump roots p q) (tail : Trail roots q z) : Trail roots p z

def Trail.path {R : Finset J} {p q : Frame J w} : Trail R p q → Path R p.carrier q.carrier
  | .nil _ => .nil _
  | .cons j tail => .cons j.step tail.path

structure Terminal (p : Frame J w) (a b c : J) (h : Nat) where
  incidence : J → BitVec h
  l : J → Fin h
  r : J → Fin h
  center : Fin h
  forwardRows : Fin h → BitVec w
  reverseRows : Fin w → BitVec h
  graphOK : ThreeNamePackedExample.endpointCheck p.ground incidence l r = true
  kernelOK : checkKernel p.ground p.words incidence forwardRows reverseRows = true
  starOK : decide ((l a = center ∨ r a = center) ∧
    (l b = center ∨ r b = center) ∧ (l c = center ∨ r c = center)) = true

theorem Terminal.kernel {p : Frame J w} {a b c : J} {h} (t : Terminal p a b c h)
    (X : Finset J) (sub : X ⊆ p.ground) :
    (∑ i ∈ X, p.carrier.col i) = 0 ↔
      (∑ i ∈ X, ThreeNameIncidenceRank.incidence t.l t.r i) = 0 := by
  have edges := ThreeNamePackedExample.endpoint_bit_sound p.ground t.incidence t.l t.r t.graphOK
  rw [← Finset.sum_congr rfl (fun i hi => edges i (sub hi))]
  exact kernel_sound t.kernelOK X sub

#print axioms Trail.path
#print axioms Terminal.kernel
end ThreeNameGenericTrail
