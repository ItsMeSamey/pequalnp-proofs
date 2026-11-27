import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi

namespace ThreeNamePacked
open scoped BigOperators

abbrev Vec (w : Nat) := Fin w → ZMod 2

/-- The least significant bit represents coordinate zero. -/
def decode {w : Nat} (word : BitVec w) : Vec w := fun j =>
  if word.getLsbD j.val then 1 else 0

theorem decode_xor {w : Nat} (a b : BitVec w) :
    decode (a ^^^ b) = decode a + decode b := by
  funext j
  simp only [decode, BitVec.getLsbD_xor, Pi.add_apply]
  cases a.getLsbD j.val <;> cases b.getLsbD j.val <;> decide

theorem decode_zero (w : Nat) : decode (0 : BitVec w) = 0 := by
  funext i
  simp [decode]

theorem decode_injective {w : Nat} : Function.Injective (@decode w) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have eq := congrFun h ⟨i, hi⟩
  change (if a.getLsbD i then (1 : ZMod 2) else 0) =
         (if b.getLsbD i then (1 : ZMod 2) else 0) at eq
  cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp [ha, hb] at eq ⊢

def xorSum {w : Nat} : List (BitVec w) → BitVec w
  | [] => 0
  | x :: xs => x ^^^ xorSum xs

theorem decode_xorSum {w : Nat} (xs : List (BitVec w)) :
    decode (xorSum xs) = (xs.map decode).sum := by
  induction xs with
  | nil => exact decode_zero w
  | cons x xs ih => simp [xorSum, decode_xor, ih]

/-- One packed row per output coordinate. -/
def applyRows {w h : Nat} (rows : Fin h → BitVec w) (v : Vec w) : Vec h :=
  fun i => ∑ j, decode (rows i) j * v j

def rowHom {w h : Nat} (rows : Fin h → BitVec w) : Vec w →+ Vec h where
  toFun := applyRows rows
  map_zero' := by funext i; simp [applyRows]
  map_add' := by intro a b; funext i; simp [applyRows, mul_add, Finset.sum_add_distrib]

def checkMap {E : Type*} {w h : Nat} (ground : Finset E)
    (a : E → BitVec w) (b : E → BitVec h) (rows : Fin h → BitVec w) : Bool :=
  decide (∀ e ∈ ground, ∀ j, applyRows rows (decode (a e)) j = decode (b e) j)

def checkKernel {E : Type*} {w h : Nat} (ground : Finset E)
    (a : E → BitVec w) (b : E → BitVec h)
    (forward : Fin h → BitVec w) (backward : Fin w → BitVec h) : Bool :=
  checkMap ground a b forward && checkMap ground b a backward

theorem applyRows_sum {E : Type*} {w h : Nat} (rows : Fin h → BitVec w)
    (s : Finset E) (v : E → Vec w) :
    applyRows rows (∑ e ∈ s, v e) = ∑ e ∈ s, applyRows rows (v e) :=
  map_sum (rowHom rows) v s

theorem map_sound {E : Type*} {w h : Nat} {g : Finset E}
    {a : E → BitVec w} {b : E → BitVec h} {rows : Fin h → BitVec w}
    (ok : checkMap g a b rows = true) (s : Finset E) (sub : s ⊆ g) :
    applyRows rows (∑ e ∈ s, decode (a e)) = ∑ e ∈ s, decode (b e) := by
  rw [applyRows_sum]
  apply Finset.sum_congr rfl
  intro e he
  apply funext
  exact (of_decide_eq_true ok) e (sub he)

theorem kernel_sound {E : Type*} {w h : Nat} {g : Finset E}
    {a : E → BitVec w} {b : E → BitVec h}
    {f : Fin h → BitVec w} {r : Fin w → BitVec h} (ok : checkKernel g a b f r = true)
    (s : Finset E) (sub : s ⊆ g) :
    (∑ e ∈ s, decode (a e)) = 0 ↔ (∑ e ∈ s, decode (b e)) = 0 := by
  obtain ⟨hf, hr⟩ := Bool.and_eq_true_iff.mp ok
  constructor
  · intro z
    rw [← map_sound hf s sub, z]
    exact (rowHom f).map_zero
  · intro z
    rw [← map_sound hr s sub, z]
    exact (rowHom r).map_zero

section Controls
private def sourceCols (i : Fin 3) : BitVec 2 := if i = 0 then 1 else if i = 1 then 2 else 3
private def targetCols (i : Fin 3) : BitVec 2 := if i = 0 then 1 else if i = 1 then 3 else 2
private def shearRows (i : Fin 2) : BitVec 2 := if i = 0 then 3 else 2
example : checkKernel Finset.univ sourceCols targetCols shearRows shearRows = true := by decide
example : checkKernel Finset.univ sourceCols targetCols shearRows (fun _ => 0) = false := by decide
end Controls

#print axioms kernel_sound
end ThreeNamePacked
