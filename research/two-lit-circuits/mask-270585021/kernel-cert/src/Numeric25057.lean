import Std
namespace Numeric25057
abbrev State := List Nat
abbrev Key := Nat × Nat × State
def goal : Nat := 302717
def ones : Nat := 2097151
def start : State := [63, 1986, 30852, 233736, 860688, 1721376]
def produced (s : State) (a : Nat) (j : Option Nat) (y : Nat) : List State :=
  if y == 0 || y == ones || s.contains y then [] else
  let withA : List State := [s.erase a, s]
  let tails : List State := match j with
    | none => withA
    | some z => withA.flatMap fun (v : State) => [v.erase z, v]
  tails.map fun v => (y :: v).mergeSort

def next (b t : Nat) (s : State) : List Key :=
  let unary := if t == 0 then [] else s.flatMap fun a =>
    (produced s a none (ones ^^^ a)).map fun v => (b,t-1,v)
  let binary := if b == 0 then [] else s.flatMap fun a => s.flatMap fun z =>
    if z < a then [a &&& z,a ||| z].flatMap fun y =>
      (produced s a (some z) y).map fun v => (b-1,t,v)
    else []
  unary ++ binary
def pairCut (s : State) (p n : Nat) (mono : Bool) : Bool :=
  p < 21 && n < 21 && goal.testBit p && !goal.testBit n &&
    s.all (fun x => if mono then !(x.testBit p && !x.testBit n)
                    else x.testBit p == x.testBit n)

def sole (s : State) (x p n : Nat) (positive : Bool) : Bool :=
  p < 21 && n < 21 && goal.testBit p && !goal.testBit n &&
    x.testBit p == positive && x.testBit n == !positive &&
    s.all (fun y => y == x || y.testBit p == y.testBit n)

def badW (b t : Nat) (s : State) (w : Nat) : Bool :=
  let tag := w % 4
  let z := w / 4
  let p := z % 32
  let n := z / 32 % 32
  let p' := z / 1024 % 32
  let n' := z / 32768 % 32
  let ix := z / 1048576
  match tag with
  | 0 => b+1 < s.length
  | 1 => pairCut s p n false
  | 2 => t == 0 && pairCut s p n true
  | _ => b+1 == s.length && match s[ix]? with
    | none => false
    | some x => sole s x p n true && sole s x p' n' false

def checkChild (table : Array Key) (k : Key) (code : Nat) : Bool :=
  if code % 2 == 0 then table[code/2]? == some k
  else badW k.1 k.2.1 k.2.2 (code/2)

def checkChildren (table : Array Key) : List Key → List Nat → Bool
  | [], [] => true
  | k :: ks, w :: ws => checkChild table k w && checkChildren table ks ws
  | _, _ => false

def checkRow (table : Array Key) (i : Nat) (proof : List Nat) : Bool :=
  match table[i]? with
  | none => false
  | some (b,t,s) =>
    let children := next b t s
    !s.contains goal && checkChildren table children proof
end Numeric25057
