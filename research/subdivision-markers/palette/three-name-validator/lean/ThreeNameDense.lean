import ThreeNameCheckEncoding
import ThreeNameValidator

namespace ThreeNameDense
open ThreeNameCheckEncoding ThreeNameValidator ThreeNameGenericTrail ThreeNameCheckTrail

structure DenseInput where
  n : Nat
  w : Nat
  columns : List Int
  pins : List Int
  names : List Int
  deriving Repr

structure DenseFrame where
  ground : List Int
  words : List Int
  deriving Repr

structure DenseJump where
  next : DenseFrame
  retained : List Int
  rows : List Int
  interface : List Int
  deriving Repr

structure DenseGraph where
  incidence : List Int
  left : List Int
  right : List Int
  center : Int
  forwardRows : List Int
  reverseRows : List Int
  deriving Repr

structure DenseStar where
  sites : Nat
  vertices : Nat
  pivots : List (Int × Int)
  supports : List (List Int)
  initial : DenseFrame
  roots : List Int
  attach : List Int
  jumps : List DenseJump
  graph : DenseGraph
  deriving Repr

inductive DenseCertificate where
  | positive (selected witness rowA rowB : List Int)
  | conflict (u v y : Bool) (witness : List Int)
  | outside (row : List Int)
  | star (data : DenseStar)
  deriving Repr

def inputFields (d : DenseInput) (t : Input d.n d.w) : Prop :=
  (List.ofFn t.columns).map (fun v => (v.toNat : Int)) = d.columns ∧
  t.pins.map (fun i => (i.val : Int)) = d.pins ∧
  [(t.target.toNat : Int), (t.tagA.toNat : Int), (t.tagB.toNat : Int)] = d.names

private def finishInput {n w : Nat} (col : Fin n → BitVec w) (pins : List (Fin n)) :
    List (BitVec w) → Option (Input n w)
  | [t,a,b] => if ([t,a,b,t ^^^ a,t ^^^ b,a ^^^ b,t ^^^ a ^^^ b].contains 0) then none
               else some ⟨col,pins,t,a,b⟩
  | _ => none

def readInput (d : DenseInput) : Option (Input d.n d.w) := do
  let cols ← readColumns d.n d.w d.columns
  let pins ← readDistinctIds d.n d.pins
  let names ← readWords d.w d.names
  finishInput cols pins names

theorem readInput_sound {d : DenseInput} {t : Input d.n d.w}
    (ok : readInput d = some t) : inputFields d t := by
  unfold readInput at ok
  cases hc : readColumns d.n d.w d.columns with
  | none => simp [hc] at ok
  | some cols =>
    cases hp : readDistinctIds d.n d.pins with
    | none => simp [hc,hp] at ok
    | some pins =>
      cases hn : readWords d.w d.names with
      | none => simp [hc,hp,hn] at ok
      | some names =>
        simp only [hc,hp,hn,bind,Option.bind] at ok
        rcases names with _ | ⟨x,_ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩⟩ <;> try contradiction
        simp only [finishInput] at ok
        split at ok
        · contradiction
        · cases ok
          exact ⟨readColumns_sound hc,(readDistinctIds_sound hp).2,readWords_sound hn⟩

def readFrame (s w : Nat) (d : DenseFrame) : Option (Frame (Fin s) w) := do
  let ground ← readDistinctIds s d.ground
  let cols ← readColumns s w d.words
  pure ⟨ground.toFinset,cols⟩

def readJump (s w : Nat) (d : DenseJump) : Option (RawJump (Fin s) w) := do
  let next ← readFrame s w d.next
  let keep ← readDistinctIds s d.retained
  let rows ← readColumns w w d.rows
  let boundary ← readWords w d.interface
  guard (decide boundary.Nodup)
  pure ⟨next,keep.toFinset,rows,boundary.toFinset⟩

def readGraph (s w h : Nat) (d : DenseGraph) : Option (RawTerminal (Fin s) w h) := do
  let cols ← readColumns s h d.incidence
  let l ← asTable s (← readIds h d.left)
  let r ← asTable s (← readIds h d.right)
  let x ← readId h d.center
  let f ← readColumns h w d.forwardRows
  let b ← readColumns w h d.reverseRows
  pure ⟨cols,l,r,x,f,b⟩

def readStar (n w : Nat) (d : DenseStar) : Option (Star n w) := do
  let table ← d.pivots.mapM (fun (j,p) => do
    let ix ← readId w j
    let v ← readWord w p
    pure (ix,v))
  let masks ← asTable w (← d.supports.mapM (readIds n))
  let initial ← readFrame d.sites w d.initial
  let [a,b,c] ← readDistinctIds d.sites d.roots | none
  let inj ← readAttachment n d.sites d.attach
  let jumps ← d.jumps.mapM (readJump d.sites w)
  let graph ← readGraph d.sites w d.vertices d.graph
  pure ⟨d.sites,d.vertices,table,masks,initial,a,b,c,inj,jumps,graph⟩

def readCertificate (n w : Nat) : DenseCertificate → Option (Certificate n w)
  | .positive S M r t => do
    let ids ← readDistinctIds n S
    let mask ← readIds n M
    let a ← readIds w r
    let b ← readIds w t
    pure (.positive ids mask a b)
  | .conflict a b t M => do
    let mask ← readIds n M
    pure (.conflict a b t mask)
  | .outside r => do
    let a ← readIds w r
    pure (.outside a)
  | .star s => do
    let star ← readStar n w s
    pure (.star star)

/-- none covers malformed data and failed certificates. A successful Bool
is the verified mathematical decision, including a verified negative. -/
def check (d : DenseInput) (proofData : DenseCertificate) : Option Bool := do
  let input ← readInput d
  let c ← readCertificate d.n d.w proofData
  if validate input c then some c.claim else none

theorem check_sound (d : DenseInput) (proofData : DenseCertificate) (answer : Bool)
    (ok : check d proofData = some answer) :
    ∃ input : Input d.n d.w, readInput d = some input ∧ (ExistsExact input ↔ answer = true) := by
  unfold check at ok
  cases hi : readInput d with
  | none => simp [hi] at ok
  | some input =>
    cases hc : readCertificate d.n d.w proofData with
    | none => simp [hi,hc] at ok
    | some c =>
      simp only [hi,hc,bind,Option.bind] at ok
      split at ok
      · rename_i h
        cases ok
        exact ⟨input,rfl,ThreeNameValidator.sound input c h⟩
      · contradiction

theorem check_sound_for {d : DenseInput} {input : Input d.n d.w} {c : DenseCertificate}
    {answer : Bool} (decoded : readInput d = some input) (ok : check d c = some answer) :
    ExistsExact input ↔ answer = true := by
  obtain ⟨v,hv,hs⟩ := check_sound d c answer ok
  rw [decoded] at hv
  cases hv
  exact hs

#print axioms readInput_sound
#print axioms check_sound
end ThreeNameDense
