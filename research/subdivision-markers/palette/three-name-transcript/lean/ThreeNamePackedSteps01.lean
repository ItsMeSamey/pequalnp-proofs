import ThreeNamePacked
import ThreeNameProjectionStep
namespace ThreeNamePackedExample
open ThreeNamePacked ThreeNameChain ThreeNameSplitCircuit
open scoped BigOperators
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
abbrev I := Fin 18
def words (i : I) : BitVec 7 := ([4, 8, 13, 12, 5, 9, 4, 5, 16, 20, 24, 32, 36, 64, 4, 4, 8, 12] : List (BitVec 7)).getD i.val 0
def roots : Finset I := {0,1,2}
def diagonal {w : Nat} (m : BitVec w) : Vec w →+ Vec w where
  toFun u i := if m.getLsbD i.val then u i else 0
  map_zero' := by funext i; simp
  map_add' := by
    intro u v; funext i
    change (if m.getLsbD i.val then u i + v i else 0) =
      (if m.getLsbD i.val then u i else 0) + (if m.getLsbD i.val then v i else 0)
    cases m.getLsbD i.val <;> simp

theorem diagonal_decode {w : Nat} (m x : BitVec w) :
    diagonal m (decode x) = decode (x &&& m) := by
  funext i
  change (if m.getLsbD i.val then (if x.getLsbD i.val then (1 : ZMod 2) else 0) else 0) = _
  simp only [decode, BitVec.getLsbD_and]
  cases m.getLsbD i.val <;> cases x.getLsbD i.val <;> rfl

def diagonalChecks {J : Type} [DecidableEq J] {w : Nat} (words : J → BitVec w)
    (old new roots x : Finset J) (m : BitVec w) (t : Finset (BitVec w)) : Bool :=
  decide (roots ⊆ x ∧ x ⊆ new ∧
    (∀ i ∈ x, words i &&& m = words i) ∧
    (∀ i ∈ old \ x, words i &&& m ∈ t) ∧ 0 ∈ t ∧
    (∀ a ∈ t, ∀ b ∈ t, a ^^^ b ∈ t) ∧
    (∀ a ∈ t, a ≠ 0 → ∃ i ∈ new, i ∉ old ∧ words i = a))

def diagonalStep {J : Type} [DecidableEq J] {w : Nat} (words : J → BitVec w)
    (old new roots x : Finset J) (m : BitVec w) (t : Finset (BitVec w))
    (ok : diagonalChecks words old new roots x m t = true) :
    Step roots ⟨old,fun i => decode (words i)⟩ ⟨new,fun i => decode (words i)⟩ := by
  unfold diagonalChecks at ok
  obtain ⟨hr, hk, hf, hy, hz, ha, hc⟩ := of_decide_eq_true ok
  apply ThreeNameProjectionStep.tableStep roots x _ _ (diagonal m) (t.image decode) hr hk
  · exact fun _ _ => rfl
  · intro i hi
    exact (diagonal_decode m (words i)).trans (congrArg decode (hf i hi))
  · intro i hi
    rw [show diagonal m ((⟨old,fun j => decode (words j)⟩ : Carrier J (Vec w)).col i) =
      decode (words i &&& m) from diagonal_decode m (words i)]
    exact Finset.mem_image_of_mem decode (hy i hi)
  · rw [← decode_zero w]
    exact Finset.mem_image_of_mem decode hz
  · intro a aMem b bMem
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp aMem
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp bMem
    rw [← decode_xor]
    exact Finset.mem_image_of_mem decode (ha u hu v hv)
  · intro a aMem nonzero
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp aMem
    have un : u ≠ 0 := fun h => nonzero ((congrArg decode h).trans (decode_zero w))
    obtain ⟨i, hi, hold, heq⟩ := hc u hu un
    exact ⟨i,hi,hold,congrArg decode heq⟩

def g0 : Finset I := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (I)).toFinset
def p0 : Carrier I (Vec 7) := ⟨g0,fun e => decode (words e)⟩
def g1 : Finset I := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List (I)).toFinset
def p1 : Carrier I (Vec 7) := ⟨g1,fun e => decode (words e)⟩
def g2 : Finset I := ([0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 14] : List (I)).toFinset
def p2 : Carrier I (Vec 7) := ⟨g2,fun e => decode (words e)⟩
def g3 : Finset I := ([0, 1, 2, 3, 4, 5, 7, 14, 15, 16, 17] : List (I)).toFinset
def p3 : Carrier I (Vec 7) := ⟨g3,fun e => decode (words e)⟩
def x0 : Finset I := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List (I)).toFinset
def rows0 (i : Fin 7) : BitVec 7 := ([1, 0, 4, 8, 16, 32, 0] : List (BitVec 7)).getD i.val 0
def tab0 : Finset (BitVec 7) := ([0] : List (BitVec 7)).toFinset
def step0 : Step roots p0 p1 :=
  diagonalStep words g0 g1 roots x0 61 tab0 (by decide)
def x1 : Finset I := ([0, 1, 2, 3, 4, 5, 7, 8, 9, 10] : List (I)).toFinset
def rows1 (i : Fin 7) : BitVec 7 := ([1, 0, 4, 8, 16, 0, 0] : List (BitVec 7)).getD i.val 0
def tab1 : Finset (BitVec 7) := ([0, 4] : List (BitVec 7)).toFinset
def step1 : Step roots p1 p2 :=
  diagonalStep words g1 g2 roots x1 29 tab1 (by decide)
end ThreeNamePackedExample
