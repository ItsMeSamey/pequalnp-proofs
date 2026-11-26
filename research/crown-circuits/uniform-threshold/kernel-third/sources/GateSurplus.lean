import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Finset.Card


namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds
abbrev Frontier := Finset Nat

/-- Add one occurrence to each demand set. Duplicate arcs cost a collision. -/
private theorem ins_le {A B : Frontier} (sub : B ⊆ A) (j : Nat) :
    (insert j A).card + B.card ≤ (insert j B).card + A.card := by
  by_cases ha : j ∈ A
  · rw [Finset.insert_eq_of_mem ha]
    have := Finset.card_le_card (Finset.subset_insert j B)
    omega
  · have hb : j ∉ B := fun h => ha (sub h)
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb]
    omega

private theorem ins_one (A : Frontier) (j : Nat) :
    (insert j A).card ≤ A.card + 1 := by
  by_cases h : j ∈ A
  · rw [Finset.insert_eq_of_mem h]; omega
  · rw [Finset.card_insert_of_notMem h]

inductive Mode where | both | left | right
deriving DecidableEq, Repr

def parents (x y : Nat) (s : Frontier) := insert x (insert y s)
def retain (m : Mode) (x y : Nat) (s : Frontier) := match m with
  | .both => parents x y s
  | .left => insert x s
  | .right => insert y s
def price : Mode → Nat | .both => 1 | _ => 0

private theorem retained_step {A B : Frontier} (sub : B ⊆ A) (x y : Nat) (m : Mode) :
    (parents x y A).card + B.card + price m ≤ (retain m x y B).card + A.card + 1 := by
  cases m with
  | both =>
    have h := ins_le sub y
    have h' := ins_le (Finset.insert_subset_insert y sub) x
    simp only [parents, retain, price]; omega
  | left =>
    have h := ins_le sub x
    have h' := ins_one (insert x A) y
    simp only [parents, retain, price, Nat.add_zero]
    rw [Finset.insert_comm x y A]; omega
  | right =>
    have h := ins_le sub y
    have h' := ins_one (insert y A) x
    simp only [parents, retain, price, Nat.add_zero]; omega

/-- A reverse liveness scan of the actual indexed circuit. Full and pruned cones
start at the same output. A one-parent operation is a wire bypass, not a gate. -/
structure Counts where
  full : Frontier
  kept : Frontier
  fullGates : Nat
  keptGates : Nat

def step (j x y : Nat) (m : Mode) (s : Counts) : Counts :=
  if j ∈ s.full then
    if j ∈ s.kept then
      ⟨parents x y (s.full.erase j), retain m x y (s.kept.erase j),
        s.fullGates+1,s.keptGates+price m⟩
    else ⟨parents x y (s.full.erase j),s.kept,s.fullGates+1,s.keptGates⟩
  else s

def Good (s : Counts) : Prop :=
  s.kept ⊆ s.full ∧ s.keptGates + s.full.card ≤ s.fullGates + s.kept.card

theorem step_good (j x y : Nat) (m : Mode) (s : Counts) (h : Good s) :
    Good (step j x y m s) := by
  obtain ⟨sub,h⟩ := h
  by_cases ha : j ∈ s.full
  · have ca := Finset.card_erase_add_one ha
    by_cases hb : j ∈ s.kept
    · have cb := Finset.card_erase_add_one hb
      have hs := Finset.erase_subset_erase j sub
      have d := retained_step hs x y m
      simp only [step, ha, hb, ite_true, Good]
      constructor
      · cases m <;> simp [retain, parents, Finset.insert_subset_iff,hs.trans
          ((Finset.subset_insert y _).trans (Finset.subset_insert x _))]
      · omega
    · have hs : s.kept ⊆ s.full.erase j := by
        intro a hm
        exact Finset.mem_erase.mpr ⟨fun e => hb (e ▸ hm),sub hm⟩
      have d := ins_one (s.full.erase j) y
      have d' := ins_one (insert y (s.full.erase j)) x
      simp only [step, ha, hb, ite_true, ite_false, Good, parents]
      exact ⟨hs.trans ((Finset.subset_insert y _).trans (Finset.subset_insert x _)), by omega⟩
  · simpa only [step, ha, ite_false, Good] using And.intro sub h

/-- The parent pair is only consulted on valid exact-binary gate cones. -/
def inputs (g : Gate) := (g.inputs.getD 0 0, g.inputs.getD 1 0)
def scan (C : Circuit) (n : Nat) (mode : Nat → Mode) : Counts :=
  (C.gates.zipIdx.reverse).foldl (fun s (g,i) =>
    step (n+i) (inputs g).1 (inputs g).2 (mode (n+i)) s)
    ⟨{C.output},{C.output},0,0⟩

theorem scan_good (C : Circuit) (n : Nat) (mode : Nat → Mode) :
    Good (scan C n mode) := by
  let f := fun (s : Counts) (z : Gate × Nat) =>
    step (n+z.2) (inputs z.1).1 (inputs z.1).2 (mode (n+z.2)) s
  have aux (l : List (Gate × Nat)) (s : Counts) (h : Good s) : Good (l.foldl f s) := by
    induction l generalizing s with
    | nil => exact h
    | cons a as ih => exact ih _ (step_good _ _ _ _ _ h)
  exact aux _ _ ⟨Finset.Subset.rfl,by simp⟩
#print axioms scan_good
end ResidualSurplus


namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds

/-- Abstract AND/OR operand, with "open" for an unpinned wire. -/
abbrev Tag := Option Bool
inductive Op where | and | or deriving DecidableEq
def act : Op → Bool → Bool → Bool | .and => (· && ·) | .or => (· || ·)
def neutral : Op → Bool | .and => true | .or => false
def gateOp : Op → GateOp | .and => .and | .or => .or
def binary (o : Op) (l r : Nat) : Gate := ⟨gateOp o, [l,r]⟩
def holds : Tag → Bool → Prop | none,_ => True | some a,b => a=b
inductive Use where | both | left | right deriving DecidableEq
def foldUse (o : Op) (l r : Tag) : Use :=
  if l == some (neutral o) then .right
  else if r == some (neutral o) then .left
  else .both
def foldTag (o : Op) : Tag → Tag → Tag
  | some a,some b => some (act o a b)
  | some a,none | none,some a => if a == neutral o then none else some a
  | none,none => none
def select : Use → Op → Bool → Bool → Bool
  | .left,_,a,_ => a
  | .right,_,_,b => b
  | .both,o,a,b => act o a b

theorem fold_sound (o : Op) (l r : Tag) (a b : Bool) (ha : holds l a) (hb : holds r b) :
    select (foldUse o l r) o a b = act o a b ∧ holds (foldTag o l r) (act o a b) := by
  cases o <;> cases l with | none | some v <;> (try cases v) <;>
    cases r with | none | some w <;> (try cases w) <;>
    cases a <;> cases b <;> simp_all [select,foldUse,foldTag,neutral,holds,act]

theorem children_open (o : Op) (l r : Tag) (h : foldTag o l r = none) :
    match foldUse o l r with
    | .both => l = none ∧ r = none
    | .left => l = none
    | .right => r = none := by
  cases o <;> cases l with | none | some v <;> (try cases v) <;>
    cases r with | none | some w <;> (try cases w) <;> simp_all [foldUse,foldTag,neutral,act]

/-- Physical constant or live operand. Lowering a surviving gate uses exactly
one new binary gate when both children are open, and zero otherwise. -/
inductive Wire where | const (b : Bool) | live (i : Nat) deriving DecidableEq
def read (w : List Bool) : Wire → Bool | .const b => b | .live i => w.getD i false
def lower (o : Op) (l r : Wire) (n : Nat) : List Gate × Wire :=
  match l,r with
  | .const a,.const b => ([],.const (act o a b))
  | .const a,.live i | .live i,.const a =>
      ([],if a == neutral o then .live i else .const a)
  | .live i,.live j => ([binary o i j], .live n)

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun z g => z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]) w

private theorem binary_val (o : Op) (a b : Nat) (w : List Bool) :
    run [binary o a b] w = w ++ [act o (w.getD a false) (w.getD b false)] := by
  cases o <;> simp [run,binary,gateOp, GateOp.eval,act]

theorem getD_new (w : List Bool) (v : Bool) : (w++[v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem lower_sound (o : Op) (l r : Wire) (w : List Bool) :
    let z := lower o l r w.length
    read (run z.1 w) z.2 = act o (read w l) (read w r) := by
  cases l with
  | const a =>
    cases r with
    | const b => rfl
    | live j => cases a <;> cases o <;> simp [run,lower,read,neutral,act]
  | live i =>
    cases r with
    | const b => cases b <;> cases o <;> simp [run,lower,read,neutral,act]
    | live j => simp [lower,read,binary_val]

end ResidualSurplus

namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds

/-- A physical indexed gate plus its local bypass choice. -/
structure Row where
  op : Op
  x : Nat
  y : Nat
  use : Use

def Row.full (r : Row) := binary r.op r.x r.y
def Row.pruned (r : Row) : Gate :=
  match r.use with
  | .both => r.full
  | .left => ⟨.or,[r.x]⟩
  | .right => ⟨.or,[r.y]⟩

def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem row_full (r : Row) (w : List Bool) :
    val r.full w = act r.op (w.getD r.x false) (w.getD r.y false) := by
  cases r with | mk o x y u =>
    cases o <;> simp [val, Row.full, binary, gateOp, GateOp.eval, act]

private theorem row_pruned (r : Row) (w : List Bool) :
    val r.pruned w = select r.use r.op (w.getD r.x false) (w.getD r.y false) := by
  cases r with | mk o x y u =>
    cases u <;> cases o <;> simp [val, Row.pruned, Row.full,binary,gateOp,GateOp.eval,act,select]

/-- Input pinning is represented by tags sound on a particular assignment. Forward
propagation supplies one choice of bypass per gate for *all* such assignments. -/
def tagRead (ts : List Tag) (i : Nat) := ts.getD i (some false)
def Fits (ts : List Tag) (w : List Bool) : Prop :=
  ts.length = w.length ∧ ∀ i, holds (tagRead ts i) (w.getD i false)

private theorem fits_append {ts : List Tag} {w : List Bool} (h : Fits ts w)
    {t : Tag} {b : Bool} (hb : holds t b) : Fits (ts++[t]) (w++[b]) := by
  obtain ⟨hn,h⟩ := h
  constructor
  · simpa using hn
  intro i
  by_cases hl : i < ts.length
  · have hl' : i < w.length := hn ▸ hl
    simpa [tagRead, List.getD_eq_getElem?_getD, List.getElem?_append,hl,hl'] using h i
  · have hl' : ¬i < w.length := hn ▸ hl
    by_cases eq : i = ts.length
    · subst i
      simpa [tagRead,List.getD_eq_getElem?_getD,List.getElem?_append,hn] using hb
    · have nz : i-ts.length ≠ 0 := by omega
      have nz' : i-w.length ≠ 0 := by omega
      cases e : i-ts.length with
      | zero => contradiction
      | succ k =>
        simp [tagRead,List.getD_eq_getElem?_getD,List.getElem?_append,hl,← hn,e,holds]

abbrev Raw := Op × Nat × Nat
def annotate : List Raw → List Tag → List Row
  | [],_ => []
  | (o,x,y)::gs,ts =>
    let l := tagRead ts x
    let r := tagRead ts y
    ⟨o,x,y,foldUse o l r⟩ :: annotate gs (ts++[foldTag o l r])

theorem run_annotation (gs : List Raw) (ts : List Tag) (w : List Bool) (h : Fits ts w) :
    run ((annotate gs ts).map Row.pruned) w = run ((annotate gs ts).map Row.full) w := by
  induction gs generalizing ts w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨o,x,y⟩ := g
    let l := tagRead ts x
    let r := tagRead ts y
    let z : Row := ⟨o,x,y,foldUse o l r⟩
    have hh := fold_sound o l r (w.getD x false) (w.getD y false) (h.2 x) (h.2 y)
    have hv : val z.pruned w = val z.full w := (row_pruned z w).trans (hh.1.trans (row_full z w).symm)
    have ht : holds (foldTag o l r) (val z.full w) := (row_full z w) ▸ hh.2
    change run ((annotate gs (ts++[foldTag o l r])).map Row.pruned) (w++[val z.pruned w]) =
      run ((annotate gs (ts++[foldTag o l r])).map Row.full) (w++[val z.full w])
    rw [hv]
    exact ih _ _ (fits_append h ht)

theorem circuit_eval_annotation (gs : List Raw) (out : Nat) (ts : List Tag) (w : List Bool)
    (h : Fits ts w) :
    Circuit.eval ⟨(annotate gs ts).map Row.pruned,out⟩ w =
    Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ w := by
  exact congrArg (fun ws : List Bool => ws.getD out false) (run_annotation gs ts w h)
#print axioms circuit_eval_annotation
end ResidualSurplus

namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds
def useMode : Use → Mode | .both => .both | .left => .left | .right => .right
/-- A bank of k compact physical gates realizes every demanded column on all
assignments in the chosen (possibly restricted) sample domain. -/
def Bank {α : Type} (n : Nat) (ins : α → List Bool) (X : Nat → α → Bool)
    (F : Frontier) (k : Nat) : Prop :=
  ∃ (gs : List Gate) (wire : Nat → Nat), gs.length = k ∧
    (∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length = 2) ∧
    ∀ i ∈ F, wire i < n+k ∧ ∀ a, (run gs (ins a)).getD (wire i) false = X i a

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w++[val g w])).length = _
    rw [ih]; simp; omega

private theorem eval_appended (w : List Bool) (gs : List Gate) (g : Gate) :
    run (gs++[g]) w = run gs w ++ [val g (run gs w)] := by
  simp [run,val,List.foldl_append]

private theorem bank_row {α : Type} {n k j : Nat} {ins : α → List Bool}
    (arity : ∀ a, (ins a).length = n) {X : Nat → α → Bool} (r : Row) {F : Frontier}
    (_seen : j ∈ F) (law : ∀ a, X j a = select r.use r.op (X r.x a) (X r.y a))
    (bk : Bank n ins X (retain (useMode r.use) r.x r.y (F.erase j)) k) :
    Bank n ins X F (k+price (useMode r.use)) := by
  obtain ⟨gs,w,len,mono,h⟩ := bk
  have old {i : Nat} (hi : i ∈ F) (hne : i ≠ j) :
      i ∈ retain (useMode r.use) r.x r.y (F.erase j) := by
    have hm := Finset.mem_erase.mpr ⟨hne,hi⟩
    cases e : r.use <;> simp [retain,useMode,parents,hm]
  cases e : r.use with
  | both =>
    have hx := h r.x (by simp [e,useMode,retain,parents])
    have hy := h r.y (by simp [e,useMode,retain,parents])
    let g := binary r.op (w r.x) (w r.y)
    refine ⟨gs++[g],fun i => if i=j then n+k else w i,by simp [len,useMode,price],?_,?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with a|a
      · exact mono p a
      · simp at a; subst p; cases eo : r.op <;> simp [g,binary,gateOp,eo]
    · intro i hm
      by_cases eq : i=j
      · subst i
        refine ⟨by simp [useMode,price],?_⟩
        intro a
        have ln : (run gs (ins a)).length = n+k := by rw [run_length,arity,len]
        have vg : val g (run gs (ins a)) = act r.op (X r.x a) (X r.y a) := by
          have z := row_full (Row.mk r.op (w r.x) (w r.y) .both) (run gs (ins a))
          exact z.trans (congrArg₂ (act r.op) (hx.2 a) (hy.2 a))
        simp only [ite_true, eq_self, eval_appended,← ln,getD_new,vg]
        simpa [e,select] using (law a).symm
      · obtain ⟨lt,ok⟩ := h i (old hm eq)
        refine ⟨by simp [eq,useMode,price]; omega,?_⟩
        intro a
        have lt' : w i < (run gs (ins a)).length := by simpa [run_length,arity,len] using lt
        simpa [eq,eval_appended,List.getD_eq_getElem?_getD,List.getElem?_append,lt'] using ok a
  | left | right =>
    let v := if r.use = .left then r.x else r.y
    have hv := h v (by simp [v,e,useMode,retain])
    refine ⟨gs,fun i => if i=j then w v else w i,by simp [useMode,price,len],mono,?_⟩
    intro i hm
    by_cases eq : i=j
    · subst i
      refine ⟨by simpa [e,useMode,price] using hv.1,?_⟩
      intro a
      have hh := hv.2 a
      simpa [v,e,select] using hh.trans (by simpa [v,e,select] using (law a).symm)
    · simpa [eq,e,useMode,price] using h i (old hm eq)

abbrev Item := Nat × Row
def advance (s : Counts) (z : Item) := step z.1 z.2.x z.2.y (useMode z.2.use) s
def first (out : Nat) : Counts := ⟨{out},{out},0,0⟩
def counts (gs : List Item) (s : Counts) := gs.foldl advance s
def Local {α : Type} (X : Nat → α → Bool) (z : Item) :=
  ∀ a, X z.1 a = select z.2.use z.2.op (X z.2.x a) (X z.2.y a)

private theorem bank_reverse {α : Type} {n : Nat} {ins : α → List Bool}
    (arity : ∀ a, (ins a).length = n) {X : Nat → α → Bool} (gs : List Item)
    (s : Counts) (sub : s.kept ⊆ s.full) (laws : ∀ z ∈ gs, Local X z)
    (init : Bank n ins X (counts gs s).kept 0) :
    ∃ k, Bank n ins X s.kept k ∧ k + s.keptGates = (counts gs s).keptGates := by
  induction gs generalizing s with
  | nil => exact ⟨0,init,by simp [counts]⟩
  | cons z zs ih =>
    let s' := advance s z
    have sub' : s'.kept ⊆ s'.full := by
      have h := step_good z.1 z.2.x z.2.y (useMode z.2.use)
        {s with keptGates := 0,fullGates := s.full.card} ⟨sub,by simp⟩
      dsimp [s',advance,step] at h ⊢
      split <;> (try split) <;> simp_all [Good]
    have hz : Local X z := laws z (by simp)
    obtain ⟨k,hk,eq⟩ := ih s' sub' (fun y hy => laws y (by simp [hy])) init
    change _ = (counts zs s').keptGates at eq
    change ∃ k, _ ∧ _ = (counts zs s').keptGates
    by_cases hf : z.1 ∈ s.full
    · by_cases hr : z.1 ∈ s.kept
      · have cost : s'.keptGates = s.keptGates + price (useMode z.2.use) := by
          simp [s',advance,step,hf,hr]
        rw [cost] at eq
        refine ⟨k+price (useMode z.2.use),bank_row arity z.2 hr hz ?_,by omega⟩
        simpa only [s',advance,step,hf,hr,ite_true] using hk
      · simpa [s',advance,step,hf,hr] using (show ∃ k', Bank n ins X s'.kept k' ∧
           k'+s'.keptGates = (counts zs s').keptGates from ⟨k,hk,eq⟩)
    · simpa [s',advance,step,hf] using (show ∃ k', Bank n ins X s'.kept k' ∧
           k'+s'.keptGates = (counts zs s').keptGates from ⟨k,hk,eq⟩)

/-- Compile the surviving gates to a genuine compact indexed monotone circuit.
The supplied column laws may be checked on just the allowed assignments. All
unreplaced source labels must name real input columns; no source identification. -/
theorem physical_minor {α : Type} (n out : Nat) (ins : α → List Bool)
    (arity : ∀ a, (ins a).length = n) (X : Nat → α → Bool) (gs : List Item)
    (laws : ∀ z ∈ gs, Local X z)
    (sources : ∀ i ∈ (counts gs (first out)).kept, i < n ∧ ∀ a, (ins a).getD i false = X i a) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (ins a) = X out a) ∧
      D.size + (counts gs (first out)).full.card ≤
        (counts gs (first out)).fullGates + (counts gs (first out)).kept.card := by
  let s := first out
  have init : Bank n ins X (counts gs s).kept 0 :=
    ⟨[],id,rfl,by simp,by simpa [run] using sources⟩
  obtain ⟨k,⟨prog,w,len,mono,real⟩,hk⟩ := bank_reverse arity gs s (by exact Finset.Subset.rfl) laws init
  have well (l : List Item) (v : Counts) (h : Good v) : Good (counts l v) := by
    induction l generalizing v with
    | nil => exact h
    | cons a as ih => exact ih _ (step_good _ _ _ _ _ h)
  have h := (well gs s ⟨Finset.Subset.rfl,by simp [s,first]⟩).2
  have valOut := real out (by simp [s,first])
  refine ⟨⟨prog,w out⟩,fun g hg => ⟨(mono g hg).1, (mono g hg).2.le⟩,valOut.2,?_⟩
  change prog.length + _ ≤ _
  have hh : k = (counts gs s).keptGates := by simpa [s,first] using hk
  rw [len,hh]
  exact h

#print axioms physical_minor
end ResidualSurplus

namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds
def items : Nat → List Row → List Item
  | _,[] => []
  | n,r::rs => (n,r)::items (n+1) rs
def Valid : Nat → List Row → Prop
  | _,[] => True
  | n,r::rs => r.x < n ∧ r.y < n ∧ Valid (n+1) rs

private theorem read_earlier (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [val g w])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append,h]

private theorem read_laws (rs : List Row) (w : List Bool) (wf : Valid w.length rs) :
    ∀ z ∈ items w.length rs, let b := run (rs.map Row.pruned) w
      b.getD z.1 false = select z.2.use z.2.op (b.getD z.2.x false) (b.getD z.2.y false) := by
  induction rs generalizing w with
  | nil => simp [items]
  | cons r rs ih =>
    obtain ⟨xlt,ylt,tail⟩ := wf
    let w' := w++[val r.pruned w]
    have len : w'.length = w.length+1 := by simp [w']
    intro z hz
    rcases List.mem_cons.mp hz with eq|mem
    · subst z
      change (run (rs.map Row.pruned) w').getD w.length false = _
      have p := read_earlier (rs.map Row.pruned) w' w.length (by omega)
      have x := read_earlier (rs.map Row.pruned) w' r.x (by omega)
      have y := read_earlier (rs.map Row.pruned) w' r.y (by omega)
      change _ = select _ _ ((run (rs.map Row.pruned) w').getD r.x false)
        ((run (rs.map Row.pruned) w').getD r.y false)
      rw [p,x,y]
      simpa [w',List.getD_eq_getElem?_getD,List.getElem?_append,xlt,ylt] using row_pruned r w
    · exact ih w' (len ▸ tail) z (len ▸ mem)

private theorem all_below (rs : List Row) (n : Nat) (wf : Valid n rs) (s : Counts)
    (hs : ∀ i ∈ s.full, i < n+rs.length) :
    ∀ i ∈ (counts (items n rs).reverse s).full, i < n := by
  induction rs generalizing n s with
  | nil => simpa [counts,items] using hs
  | cons r rs ih =>
    obtain ⟨hx,hy,hw⟩ := wf
    let a := counts (items (n+1) rs).reverse s
    have bound : ∀ i ∈ a.full, i < n+1 := ih _ hw s (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs)
    change ∀ i ∈ (counts ((n,r)::items (n+1) rs).reverse s).full, i < n
    simp only [counts,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change ∀ i ∈ (advance a (n,r)).full, i < n
    by_cases hn : n ∈ a.full
    · intro i hi
      have hh : i=r.x ∨ i=r.y ∨ i∈a.full.erase n := by
        by_cases hk : n ∈ a.kept <;>
          simpa [advance,step,hn,hk,parents] using hi
      rcases hh with eq|eq|rest
      · simpa [← eq] using hx
      · simpa [← eq] using hy
      · have p := bound i (Finset.mem_erase.mp rest).2
        have q := (Finset.mem_erase.mp rest).1
        omega
    · simp only [advance,step,hn,ite_false]
      intro i hi
      have p := bound i hi
      have q : i ≠ n := fun e => hn (e ▸ hi)
      omega
/-- The full physical theorem: start with well-formed two-input AND/OR rows and
a nonconstant cofactor, compile a compact saving with actual upstream semantics.
The returned source count is the number of used formal boundary inputs. -/
theorem physical_rows {α : Type} (n out : Nat) (ins : α → List Bool)
    (arity : ∀ a, (ins a).length = n) (rows : List Row) (valid : Valid n rows)
    (output_valid : out < n+rows.length) :
    let s := counts (items n rows).reverse (first out)
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (ins a) = Circuit.eval ⟨rows.map Row.pruned,out⟩ (ins a)) ∧
      D.size + s.full.card ≤ s.fullGates + s.kept.card := by
  let X := fun i a => (run (rows.map Row.pruned) (ins a)).getD i false
  apply physical_minor n out ins arity X (items n rows).reverse
  · intro z hz a
    apply read_laws rows (ins a) (by simpa [arity] using valid) z
    simpa [arity] using hz
  · let ss := first out
    have sub (zs : List Item) (s : Counts) (g : Good s) : Good (counts zs s) := by
      induction zs generalizing s with
      | nil => exact g
      | cons z zs ih => exact ih _ (step_good _ _ _ _ _ g)
    have h0 : Good ss := ⟨Finset.Subset.rfl,by simp [ss,first]⟩
    intro i hi
    have hf := (sub (items n rows).reverse ss h0).1 hi
    have lt := all_below rows n valid ss (by simpa [ss,first] using output_valid) i hf
    exact ⟨lt,fun a => (read_earlier (rows.map Row.pruned) (ins a) i (by simpa [arity] using lt)).symm⟩

theorem constant_restriction {α : Type} (n out : Nat) (ins : α → List Bool)
    (arity : ∀ a, (ins a).length = n) (gs : List Raw) (ts : List Tag)
    (pins : ∀ a, Fits ts (ins a)) (valid : Valid n (annotate gs ts))
    (output_valid : out < n+(annotate gs ts).length) :
    let rs := annotate gs ts
    let s := counts (items n rs).reverse (first out)
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (ins a) = Circuit.eval ⟨rs.map Row.full,out⟩ (ins a)) ∧
      D.size + s.full.card ≤ s.fullGates + s.kept.card := by
  obtain ⟨D,mono,eq,sz⟩ := physical_rows n out ins arity (annotate gs ts) valid output_valid
  exact ⟨D,mono,fun a => (eq a).trans (circuit_eval_annotation gs out ts (ins a) (pins a)),sz⟩
#print axioms constant_restriction
end ResidualSurplus

namespace ResidualSurplus
/-- If certificates mark all and only the post-fold open wires, every live
source in the output minor is open. This explicitly forbids identification. -/
def KeepsOpen (Q : Nat → Prop) (z : Item) : Prop := Q z.1 →
  match z.2.use with
  | .both => Q z.2.x ∧ Q z.2.y
  | .left => Q z.2.x
  | .right => Q z.2.y

theorem open_frontier (Q : Nat → Prop) (xs : List Item) (s : Counts)
    (localOpen : ∀ z ∈ xs, KeepsOpen Q z) (known : ∀ i ∈ s.kept, Q i) :
    ∀ i ∈ (counts xs s).kept, Q i := by
  induction xs generalizing s with
  | nil => exact known
  | cons z zs ih =>
    apply ih (advance s z) (fun w hw => localOpen w (by simp [hw]))
    by_cases h : z.1 ∈ s.full
    · by_cases h' : z.1 ∈ s.kept
      · have q := localOpen z (by simp) (known _ h')
        have rest : ∀ i ∈ s.kept.erase z.1, Q i :=
          fun i hi => known _ (Finset.mem_erase.mp hi).2
        intro i hi
        cases e : z.2.use <;>
          simp [advance,step,h,h',e,retain,useMode,parents] at hi <;>
          simp [e] at q <;> grind
      · simpa [advance,step,h,h'] using known
    · simpa [advance,step,h] using known

end ResidualSurplus

namespace ResidualSurplus
def extendTags : List Raw → List Tag → List Tag
  | [],ts => ts
  | (o,x,y)::rs,ts =>
    extendTags rs (ts++[foldTag o (tagRead ts x) (tagRead ts y)])
private theorem tag_old (gs : List Raw) (ts : List Tag) (i : Nat) (hi : i < ts.length) :
    tagRead (extendTags gs ts) i = tagRead ts i := by
  induction gs generalizing ts with
  | nil => rfl
  | cons z zs ih =>
    obtain ⟨o,x,y⟩ := z
    change tagRead (extendTags zs (ts++[_])) i = _
    rw [ih _ (by simp; omega)]
    simp [tagRead,List.getD_eq_getElem?_getD,List.getElem?_append,hi]

private theorem open_laws (gs : List Raw) (ts : List Tag) (valid : Valid ts.length (annotate gs ts)) :
    ∀ z ∈ items ts.length (annotate gs ts), KeepsOpen (fun i => tagRead (extendTags gs ts) i = none) z := by
  induction gs generalizing ts with
  | nil => simp [items,annotate]
  | cons z zs ih =>
    obtain ⟨o,x,y⟩ := z
    let l := tagRead ts x
    let r := tagRead ts y
    let ts' := ts++[foldTag o l r]
    have len : ts'.length = ts.length+1 := by simp [ts']
    obtain ⟨hx,hy,tail⟩ := valid
    change x < ts.length at hx
    change y < ts.length at hy
    intro v hv
    rcases List.mem_cons.mp hv with eq|other
    · subst v
      have xo : tagRead (extendTags zs ts') x = l := by
        rw [tag_old _ _ _ (by omega)]
        simp [ts',l,tagRead,List.getD_eq_getElem?_getD,List.getElem?_append,hx]
      have yo : tagRead (extendTags zs ts') y = r := by
        rw [tag_old _ _ _ (by omega)]
        simp [ts',r,tagRead,List.getD_eq_getElem?_getD,List.getElem?_append,hy]
      have new : tagRead (extendTags zs ts') ts.length = foldTag o l r := by
        rw [tag_old _ _ _ (by omega)]
        simp [ts',tagRead,List.getD_eq_getElem?_getD]
      change tagRead (extendTags zs ts') ts.length = none → _
      intro h
      have q := children_open o l r (new ▸ h)
      change (match foldUse o l r with
        | .both => tagRead (extendTags zs ts') x = none ∧ tagRead (extendTags zs ts') y = none
        | .left => tagRead (extendTags zs ts') x = none
        | .right => tagRead (extendTags zs ts') y = none)
      cases e : foldUse o l r <;> simpa [e,xo,yo] using q
    · exact ih ts' (len ▸ tail) v (len ▸ other)

theorem surviving_unpinned (gs : List Raw) (ts : List Tag) (out : Nat)
    (valid : Valid ts.length (annotate gs ts)) (ho : tagRead (extendTags gs ts) out = none)
    (output_valid : out < ts.length+(annotate gs ts).length) :
    let s := counts (items ts.length (annotate gs ts)).reverse (first out)
    ∀ i ∈ s.kept, tagRead ts i = none := by
  let xs := items ts.length (annotate gs ts)
  have h := open_frontier (fun i => tagRead (extendTags gs ts) i = none) xs.reverse (first out)
    (fun z hz => open_laws gs ts valid z (by simpa [xs] using hz)) (by simpa [first] using ho)
  have sub (l : List Item) (s : Counts) (g : Good s) : Good (counts l s) := by
    induction l generalizing s with
    | nil => exact g
    | cons z zs ih => exact ih _ (step_good _ _ _ _ _ g)
  have start : Good (first out) := ⟨Finset.Subset.rfl,by simp [first]⟩
  change ∀ i ∈ (counts xs.reverse (first out)).kept, tagRead ts i = none
  intro i hi
  have hf := (sub xs.reverse _ start).1 hi
  have lt := all_below (annotate gs ts) ts.length valid (first out) (by simpa [first] using output_valid) i hf
  simpa [tag_old gs ts i lt] using h i hi

#print axioms surviving_unpinned
end ResidualSurplus

namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds

private theorem tag_fit_final (gs : List Raw) (ts : List Tag) (w : List Bool)
    (h : Fits ts w) :
    Fits (extendTags gs ts) (run ((annotate gs ts).map Row.full) w) := by
  induction gs generalizing ts w with
  | nil => exact h
  | cons a gs ih =>
    obtain ⟨o,x,y⟩ := a
    let l := tagRead ts x
    let r := tagRead ts y
    let z : Row := ⟨o,x,y,foldUse o l r⟩
    have q := (fold_sound o l r (w.getD x false) (w.getD y false) (h.2 x) (h.2 y)).2
    have ht : holds (foldTag o l r) (val z.full w) := (row_full z w) ▸ q
    exact ih _ _ (fits_append h ht)

/-- A semantically nonconstant output is definitely open, even when static
constant propagation misses some constant subexpressions. -/
theorem open_of_nonconstant (gs : List Raw) (ts : List Tag) (out : Nat) (u v : List Bool)
    (hu : Fits ts u) (hv : Fits ts v)
    (diff : Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ u ≠
            Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ v) :
    tagRead (extendTags gs ts) out = none := by
  have a := (tag_fit_final gs ts u hu).2 out
  have b := (tag_fit_final gs ts v hv).2 out
  cases e : tagRead (extendTags gs ts) out with
  | none => rfl
  | some p =>
    simp only [e,holds] at a b
    exact False.elim (diff (a.symm.trans b))

end ResidualSurplus

namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds
/-- Gate-budget form for a nonconstant restricted problem: when at most t
formal inputs are unpinned, a compact circuit needs at most t−1 plus the old
surplus gates. The cross-additive version avoids natural-number truncation. -/
theorem pinned_minor_bound {α : Type} (gs : List Raw) (ts : List Tag) (out : Nat)
    (ins : α → List Bool) (fit : ∀ a, Fits ts (ins a))
    (valid : Valid ts.length (annotate gs ts)) (outOK : out < ts.length + (annotate gs ts).length)
    (nonconstant : ∃ a b, Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ (ins a) ≠
                         Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ (ins b))
    (free : Frontier) (covers : ∀ i, tagRead ts i = none → i ∈ free) :
    let rs := annotate gs ts
    let s := counts (items ts.length rs).reverse (first out)
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (ins a) = Circuit.eval ⟨rs.map Row.full,out⟩ (ins a)) ∧
      D.size + s.full.card ≤ s.fullGates + free.card := by
  obtain ⟨a,b,hab⟩ := nonconstant
  have ho := open_of_nonconstant gs ts out (ins a) (ins b) (fit a) (fit b) hab
  have opn := surviving_unpinned gs ts out valid ho outOK
  obtain ⟨D,mono,val,sz⟩ := constant_restriction ts.length out ins (fun a => (fit a).1.symm)
    gs ts fit valid outOK
  have sub : (counts (items ts.length (annotate gs ts)).reverse (first out)).kept ⊆ free :=
    fun i hi => covers i (opn i hi)
  exact ⟨D,mono,val,sz.trans (Nat.add_le_add_left (Finset.card_le_card sub) _)⟩
#print axioms pinned_minor_bound
end ResidualSurplus

namespace ResidualSurplus
/-- Full rows preserve the raw gate order, operations, and both indexed operands.
The original circuit in pinned_minor_bound is independent of the pin assignment. -/
@[simp] theorem annotation_full (gs : List Raw) (ts : List Tag) :
    (annotate gs ts).map Row.full = gs.map (fun (o,x,y) => binary o x y) := by
  induction gs generalizing ts with
  | nil => rfl
  | cons z zs ih =>
    obtain ⟨o,x,y⟩ := z
    simp [annotate,Row.full,ih]
end ResidualSurplus

namespace ResidualSurplus
open PEqualNP.CircuitLowerBounds
private theorem physical_minor_map {α : Type} (n out : Nat) (ins : α → List Bool)
    (arity : ∀ a, (ins a).length = n) (X : Nat → α → Bool) (gs : List Item)
    (laws : ∀ z ∈ gs, Local X z)
    (ren : Nat → Nat) (sources : ∀ i ∈ (counts gs (first out)).kept, ren i < n ∧ ∀ a, (ins a).getD (ren i) false = X i a) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (ins a) = X out a) ∧
      D.size + (counts gs (first out)).full.card ≤
        (counts gs (first out)).fullGates + (counts gs (first out)).kept.card := by
  let s := first out
  have init : Bank n ins X (counts gs s).kept 0 :=
    ⟨[],ren,rfl,by simp,by simpa [run] using sources⟩
  obtain ⟨k,⟨prog,w,len,mono,real⟩,hk⟩ := bank_reverse arity gs s (by exact Finset.Subset.rfl) laws init
  have well (l : List Item) (v : Counts) (h : Good v) : Good (counts l v) := by
    induction l generalizing v with
    | nil => exact h
    | cons a as ih => exact ih _ (step_good _ _ _ _ _ h)
  have h := (well gs s ⟨Finset.Subset.rfl,by simp [s,first]⟩).2
  have valOut := real out (by simp [s,first])
  refine ⟨⟨prog,w out⟩,fun g hg => ⟨(mono g hg).1, (mono g hg).2.le⟩,valOut.2,?_⟩
  change prog.length + _ ≤ _
  have hh : k = (counts gs s).keptGates := by simpa [s,first] using hk
  rw [len,hh]
  exact h

/-- The compact input list may have a different arity and numbering. Each
surviving old formal input must be explicitly simulated; it is the *number of
old open names*, not the number of distinct values after projection, that is charged. -/
theorem reindexed_pinned_minor {α : Type} (gs : List Raw) (ts : List Tag) (out m : Nat)
    (large small : α → List Bool) (fit : ∀ a, Fits ts (large a))
    (arity : ∀ a, (small a).length = m) (valid : Valid ts.length (annotate gs ts))
    (outOK : out < ts.length + (annotate gs ts).length)
    (nonconstant : ∃ a b, Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ (large a) ≠
                         Circuit.eval ⟨(annotate gs ts).map Row.full,out⟩ (large b))
    (ren : Nat → Nat)
    (supply : ∀ i, tagRead ts i = none →
      ren i < m ∧ ∀ a, (small a).getD (ren i) false = (large a).getD i false)
    (free : Frontier) (covers : ∀ i, tagRead ts i = none → i ∈ free) :
    let rs := annotate gs ts
    let s := counts (items ts.length rs).reverse (first out)
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (small a) = Circuit.eval ⟨gs.map (fun (o,x,y) => binary o x y),out⟩ (large a)) ∧
      D.size + s.full.card ≤ s.fullGates + free.card := by
  obtain ⟨a,b,hab⟩ := nonconstant
  have ho := open_of_nonconstant gs ts out (large a) (large b) (fit a) (fit b) hab
  have opn := surviving_unpinned gs ts out valid ho outOK
  let rs := annotate gs ts
  let xs := (items ts.length rs).reverse
  let X := fun i a => (run (rs.map Row.pruned) (large a)).getD i false
  have wf a : Valid (large a).length rs := by simpa [(fit a).1.symm,rs] using valid
  have laws : ∀ z ∈ xs, Local X z := by
    intro z hz a
    apply read_laws rs (large a) (wf a) z
    simpa [xs,(fit a).1.symm] using hz
  have src : ∀ i ∈ (counts xs (first out)).kept,
      ren i < m ∧ ∀ a, (small a).getD (ren i) false = X i a := by
    intro i hi
    have open_ := opn i hi
    obtain ⟨bound,agree⟩ := supply i open_
    refine ⟨bound,fun a => (agree a).trans ?_⟩
    have lt : i < ts.length := by
      by_contra! ge
      simp [tagRead,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : ts.length ≤ i)] at open_
    exact (read_earlier _ _ _ (by simpa [(fit a).1.symm] using lt)).symm
  obtain ⟨D,mono,eq,sz⟩ := physical_minor_map m out small arity X xs laws ren src
  have sub : (counts xs (first out)).kept ⊆ free := fun i hi => covers i (opn i hi)
  refine ⟨D,mono,fun a => (eq a).trans ?_,sz.trans (Nat.add_le_add_left (Finset.card_le_card sub) _)⟩
  change Circuit.eval ⟨(annotate gs ts).map Row.pruned,out⟩ (large a) =
    Circuit.eval ⟨gs.map (fun (o,x,y) => binary o x y),out⟩ (large a)
  simpa only [annotation_full] using circuit_eval_annotation gs out ts (large a) (fit a)

#print axioms reindexed_pinned_minor
end ResidualSurplus
