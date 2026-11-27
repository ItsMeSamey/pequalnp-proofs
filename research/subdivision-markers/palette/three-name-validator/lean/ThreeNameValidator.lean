import ThreeNamePackedRootCheck
import ThreeNameGenericHost
import ThreeNameGenericDirect
import ThreeNameCheckTrail
namespace ThreeNameValidator
open ThreeNameGenericTrail ThreeNameCheckTrail ThreeNameGenericPositive ThreeNameGenericDirect
open ThreeNamePacked ThreeNamePinReduction

structure Input (n w : Nat) where
  columns : Fin n → BitVec w
  pins : List (Fin n)
  target : BitVec w
  tagA : BitVec w
  tagB : BitVec w

structure Star (n w : Nat) where
  sites : Nat
  vertices : Nat
  table : ThreeNamePackedPins.Table w
  supports : Fin w → List (Fin n)
  initial : Frame (Fin sites) w
  rootA : Fin sites
  rootB : Fin sites
  rootC : Fin sites
  attach : Fin n → Fin sites
  jumps : List (RawJump (Fin sites) w)
  graph : RawTerminal (Fin sites) w vertices

variable {n w : Nat}

def ExistsExact (d : Input n w) : Prop :=
  ∃ A : Finset (Fin n), d.pins.toFinset ⊆ A ∧
    Exact (fun i => decode (d.columns i)) (named d.target d.tagA d.tagB) A

def starCheck (d : Input n w) (s : Star n w) : Bool :=
  if hi : Function.Injective s.attach then
    ThreeNamePackedPins.check d.columns d.pins s.table s.supports &&
    ThreeNamePackedRootCheck.check s.initial s.rootA s.rootB s.rootC d.target d.tagA d.tagB s.table &&
    ThreeNameGenericHost.attachmentCheck d.columns d.pins s.table s.initial
      {s.rootA,s.rootB,s.rootC} ⟨s.attach,hi⟩ &&
    (ThreeNameCheckTrail.check {s.rootA,s.rootB,s.rootC} s.initial s.jumps s.rootA s.rootB s.rootC s.graph).isSome
  else false

theorem star_sound (d : Input n w) (s : Star n w) (ok : starCheck d s = true) :
    ¬ ExistsExact d := by
  unfold starCheck at ok
  split at ok
  next hi =>
    simp only [Bool.and_eq_true] at ok
    obtain ⟨⟨⟨pinOK,initOK⟩,attachOK⟩,rest⟩ := ok
    rw [ThreeNamePackedRootCheck.reflects] at initOK
    cases hr : ThreeNameCheckTrail.check {s.rootA,s.rootB,s.rootC} s.initial s.jumps
        s.rootA s.rootB s.rootC s.graph with
    | none => simp [hr] at rest
    | some result =>
      obtain ⟨q,path,g⟩ := result
      rintro ⟨A,sub,hit⟩
      exact ThreeNameGenericHost.rejects d.columns d.pins d.target d.tagA d.tagB s.table s.supports
        pinOK s.initial q s.rootA s.rootB s.rootC ⟨s.attach,hi⟩ initOK attachOK path g A sub hit
  next => contradiction
inductive Certificate (n w : Nat) where
  | positive (selected witness : List (Fin n)) (rowA rowB : List (Fin w))
  | conflict (u v y : Bool) (witness : List (Fin n))
  | outside (row : List (Fin w))
  | star (raw : Star n w)

def Certificate.claim : Certificate n w → Bool
  | .positive .. => true
  | _ => false

def validate (d : Input n w) : Certificate n w → Bool
  | .positive ids mask a b => ThreeNameGenericPositive.check d.columns d.pins ids d.target d.tagA d.tagB mask a b
  | .conflict u v y ids => checkConflict d.columns d.pins d.target d.tagA d.tagB u v y ids
  | .outside row => checkOutside d.columns d.target row
  | .star s => starCheck d s

theorem sound (d : Input n w) (c : Certificate n w) (ok : validate d c = true) :
    ExistsExact d ↔ c.claim = true := by
  cases c with
  | positive ids mask a b =>
    obtain ⟨sub,hit⟩ := ThreeNameGenericPositive.sound _ _ _ _ _ _ _ _ _ ok
    exact ⟨fun _ => rfl,fun _ => ⟨_,sub,hit⟩⟩
  | conflict u v y ids =>
    have bad := conflict_no _ _ _ _ _ _ _ _ _ ok
    constructor
    · rintro ⟨A,sub,hit⟩
      exact (bad A sub hit).elim
    · intro h
      contradiction
  | outside row =>
    have bad := outside_no d.columns d.target d.tagA d.tagB row ok
    constructor
    · rintro ⟨A,_,hit⟩
      exact (bad A hit).elim
    · intro h
      contradiction
  | star s =>
    exact ⟨fun hit => (star_sound d s ok hit).elim,fun h => by contradiction⟩

#print axioms star_sound
#print axioms sound
end ThreeNameValidator
