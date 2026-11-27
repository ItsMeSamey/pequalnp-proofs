import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Embedding.Basic

namespace ThreeNameCheckEncoding

def readId (n : Nat) : Int → Option (Fin n)
  | .negSucc _ => none
  | .ofNat x => if h : x < n then some ⟨x,h⟩ else none

def readWord (w : Nat) : Int → Option (BitVec w)
  | .negSucc _ => none
  | .ofNat x => if h : x < 2^w then some (BitVec.ofNatLT x h) else none

theorem readId_sound {n : Nat} {x : Int} {i : Fin n} (ok : readId n x = some i) :
    (i.val : Int) = x := by
  cases x with
  | negSucc n => simp [readId] at ok
  | ofNat x =>
    by_cases hx : x < n
    · simp [readId,hx] at ok
      cases ok
      rfl
    · simp [readId,hx] at ok

theorem readWord_sound {w : Nat} {x : Int} {v : BitVec w} (ok : readWord w x = some v) :
    (v.toNat : Int) = x := by
  cases x with
  | negSucc n => simp [readWord] at ok
  | ofNat x =>
    by_cases hx : x < 2^w
    · simp [readWord,hx] at ok
      cases ok
      rfl
    · simp [readWord,hx] at ok

/-- The successful list is checked against the entire original sequence,
including order, multiplicity and length. Equal columns remain separate. -/
private def readList {α : Type} (read : Int → Option α) (encode : α → Int)
    (raw : List Int) : Option (List α) := do
  let xs ← raw.mapM read
  if xs.map encode = raw then some xs else none

private theorem readList_sound {α : Type} {read : Int → Option α} {encode : α → Int}
    {raw : List Int} {xs : List α} (ok : readList read encode raw = some xs) :
    xs.map encode = raw := by
  unfold readList at ok
  cases hm : raw.mapM read with
  | none => simp [hm] at ok
  | some ys =>
    simp only [hm,bind,Option.bind] at ok
    split at ok
    · cases ok; assumption
    · contradiction

def readIds (n : Nat) := readList (readId n) (fun i => (i.val : Int))
def readWords (w : Nat) := readList (readWord w) (fun x => (x.toNat : Int))

theorem readIds_sound {n raw xs} (ok : readIds n raw = some xs) :
    xs.map (fun i => (i.val : Int)) = raw := readList_sound ok

theorem readWords_sound {w raw xs} (ok : readWords w raw = some xs) :
    xs.map (fun x => (x.toNat : Int)) = raw := readList_sound ok

def readDistinctIds (n : Nat) (raw : List Int) : Option (List (Fin n)) := do
  let ids ← readIds n raw
  if ids.Nodup then some ids else none

theorem readDistinctIds_sound {n raw xs} (ok : readDistinctIds n raw = some xs) :
    xs.Nodup ∧ xs.map (fun i => (i.val : Int)) = raw := by
  unfold readDistinctIds at ok
  cases hm : readIds n raw with
  | none => simp [hm] at ok
  | some ys =>
    simp only [hm,bind,Option.bind] at ok
    split at ok
    · cases ok; exact ⟨by assumption,readIds_sound hm⟩
    · contradiction

/-- Reification of an exact-length table as a total finite function. -/
def asTable (n : Nat) {α : Type} (xs : List α) : Option (Fin n → α) :=
  if h : xs.length = n then some (fun i => xs.get ⟨i.val,h.symm ▸ i.isLt⟩) else none

theorem asTable_sound {n : Nat} {α : Type} {xs : List α} {f : Fin n → α}
    (ok : asTable n xs = some f) : List.ofFn f = xs := by
  unfold asTable at ok
  split at ok
  · rename_i h
    subst n
    cases ok
    exact List.ofFn_get xs
  · contradiction

def readColumns (n w : Nat) (raw : List Int) : Option (Fin n → BitVec w) := do
  let xs ← readWords w raw
  asTable n xs

theorem readColumns_sound {n w raw cols} (ok : readColumns n w raw = some cols) :
    (List.ofFn cols).map (fun v => (v.toNat : Int)) = raw := by
  unfold readColumns at ok
  cases hr : readWords w raw with
  | none => simp [hr] at ok
  | some xs =>
    simp only [hr,bind,Option.bind] at ok
    rw [asTable_sound ok]
    exact readWords_sound hr

def readAttachment (n m : Nat) (raw : List Int) : Option (Fin n ↪ Fin m) := do
  let ids ← readIds m raw
  let f ← asTable n ids
  if inj : ∀ i j, f i = f j → i = j then some ⟨f,fun i j h => inj i j h⟩ else none

theorem readAttachment_sound {n m raw f} (ok : readAttachment n m raw = some f) :
    (List.ofFn (fun i => f i)).map (fun j => (j.val : Int)) = raw := by
  unfold readAttachment at ok
  cases hr : readIds m raw with
  | none => simp [hr] at ok
  | some ids =>
    simp only [hr,bind,Option.bind] at ok
    cases ht : asTable n ids with
    | none => simp [ht] at ok
    | some g =>
      simp only [ht,bind,Option.bind] at ok
      split at ok
      · cases ok
        change (List.ofFn g).map (fun j => (j.val : Int)) = raw
        rw [asTable_sound ht]
        exact readIds_sound hr
      · contradiction

example : (readAttachment 0 0 []).isSome = true := by decide
example : (readAttachment 2 4 [3,1]).isSome = true := by decide
example : (readAttachment 2 4 [1,1]).isSome = false := by decide
example : (readAttachment 2 4 [3,-1]).isSome = false := by decide
example : (readAttachment 2 4 [3,4]).isSome = false := by decide
example : (readAttachment 2 4 [3]).isSome = false := by decide
example : (readColumns 3 2 [0,3,3]).isSome = true := by decide
example : (readColumns 2 2 [0,4]).isSome = false := by decide
example : (readWord 0 0).isSome = true := by decide
example : (readWord 0 (-1)).isSome = false := by decide
example : (readDistinctIds 3 [1,1]).isSome = false := by decide

#print axioms readColumns_sound
#print axioms readAttachment_sound
end ThreeNameCheckEncoding
