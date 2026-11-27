import ThreeNameGenericRoots
import ThreeNameGenericDirect
namespace ThreeNamePackedRootCheck
open ThreeNameGenericPositive ThreeNameGenericDirect ThreeNameGenericTrail ThreeNamePacked
open scoped BigOperators
variable {J : Type} [DecidableEq J] {w : Nat}

def toBit (x : F) : Bool := decide (x = 1)
theorem rebit (x : F) : bit (toBit x) = x :=
  (show ∀ x : F, bit (toBit x) = x by decide) x

def image (table : ThreeNamePackedPins.Table w) (target a b : BitVec w)
    (z : Tags) (y : F) : Vec w :=
  decode (ThreeNamePackedPins.run table
    (namedWord target a b (toBit (z 0)) (toBit (z 1)) (toBit y)))

theorem represented (table : ThreeNamePackedPins.Table w) (target a b : BitVec w)
    (z : Tags) (y : F) :
    image table target a b z y =
      (ThreeNamePackedPins.asLinear table).comp (named target a b) (z,y) := by
  unfold image
  rw [ThreeNamePackedPins.represented,decode_namedWord,rebit]
  have hz : tagPair (toBit (z 0)) (toBit (z 1)) = z := by
    funext j
    fin_cases j <;> simp [tagPair,rebit]
  rw [hz]
  rfl

def check (p : Frame J w) (i j k : J) (target a b : BitVec w)
    (table : ThreeNamePackedPins.Table w) : Bool :=
  let R : Finset J := {i,j,k}
  decide (i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ R ⊆ p.ground ∧
    (∀ P ∈ R.powerset, P.Nonempty → (∑ e ∈ P,p.carrier.col e) ≠ 0) ∧
    image table target a b 0 1 = ∑ e ∈ R,p.carrier.col e ∧
    ∀ P ∈ R.powerset, ∃ z : Tags, ∃ y : F, image table target a b z y = ∑ e ∈ P,p.carrier.col e)

theorem reflects (p : Frame J w) (i j k : J) (target a b : BitVec w)
    (table : ThreeNamePackedPins.Table w) :
    check p i j k target a b table = ThreeNameGenericRoots.initialCheck p i j k target a b table := by
  simp only [check,ThreeNameGenericRoots.initialCheck,represented]

#print axioms reflects
end ThreeNamePackedRootCheck
