import Numeric23724
import SmallSort23724
namespace Numeric23724

def childWith (atKey : Nat → Option Key) (k : Key) (code : Nat) : Bool :=
  if code % 2 == 0 then atKey (code/2) == some k else badW k.1 k.2.1 k.2.2 (code/2)

def childrenWith (atKey : Nat → Option Key) : List Key → List Nat → Bool
  | [],[] => true
  | k::ks,w::ws => childWith atKey k w && childrenWith atKey ks ws
  | _,_ => false

def rowWith (atKey : Nat → Option Key) (i : Nat) (proof : List Nat) : Bool :=
  match atKey i with
  | none => false
  | some (b,t,s) => !s.contains goal && childrenWith atKey (next b t s) proof

theorem childWith_eq {table : Array Key} {atKey : Nat → Option Key}
    (h : ∀ i, table[i]? = atKey i) (k : Key) (w : Nat) :
    checkChild table k w = childWith atKey k w := by simp [checkChild,childWith,h]

theorem childrenWith_eq {table : Array Key} {atKey : Nat → Option Key}
    (h : ∀ i, table[i]? = atKey i) (ks : List Key) (ws : List Nat) :
    checkChildren table ks ws = childrenWith atKey ks ws := by
  induction ks generalizing ws with
  | nil => cases ws <;> rfl
  | cons k ks ih =>
    cases ws with
    | nil => rfl
    | cons w ws => simp [checkChildren, childrenWith, childWith_eq h, ih]

theorem rowWith_eq {table : Array Key} {atKey : Nat → Option Key}
    (h : ∀ i, table[i]? = atKey i) (i : Nat) (proof : List Nat) :
    checkRow table i proof = rowWith atKey i proof := by
  cases hi : atKey i with
  | none => simp [checkRow, rowWith, h, hi]
  | some k => rcases k with ⟨b,t,s⟩; simp [checkRow, rowWith, h, hi, childrenWith_eq h]
def rowEval (atKey : Nat → Option Key) (i : Nat) (proof : List Nat) : Bool :=
  match atKey i with
  | none => false
  | some (b,t,s) =>
    let make := fun (a : Nat) (j : Option Nat) (y : Nat) =>
      if y == 0 || y == ones || s.contains y then [] else
      let vs : List State := [s.erase a,s]
      let tails := match j with
        | none => vs
        | some z => vs.flatMap fun (v : State) => [v.erase z,v]
      tails.map fun v => insSort (y :: v)
    let un := if t == 0 then [] else s.flatMap fun a =>
      (make a none (ones ^^^ a)).map fun v => (b,t-1,v)
    let bi := if b == 0 then [] else s.flatMap fun a => s.flatMap fun z =>
      if z < a then [a &&& z,a ||| z].flatMap fun y =>
        (make a (some z) y).map fun v => (b-1,t,v)
      else []
    !s.contains goal && childrenWith atKey (un ++ bi) proof

theorem rowWith_eval (atKey : Nat → Option Key) (i : Nat) (p : List Nat) :
    rowWith atKey i p = rowEval atKey i p := by
  cases h : atKey i with
  | none => simp [rowWith,rowEval,h]
  | some k =>
    rcases k with ⟨b,t,s⟩
    simp only [rowWith,rowEval,h,next,produced,mergeSort_eq_insSort]

end Numeric23724
