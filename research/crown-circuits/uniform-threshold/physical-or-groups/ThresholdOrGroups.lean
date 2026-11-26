import GateSurplus
import Mathlib.Data.Finset.Card
open PEqualNP.CircuitLowerBounds
open ResidualSurplus
namespace ThresholdOrGroups

def isOr (g : Gate) : Bool := match g.op with | .or => true | _ => false
def ors (gs : List Gate) := gs.countP isOr
def Mono (gs : List Gate) := ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length = 2

private theorem length_run (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).length = _
    rw [ih]; simp; omega

private theorem earlier (gs : List Gate) (w : List Bool) (i : Nat) (lt : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append,lt]

private theorem appended (gs hs : List Gate) (w : List Bool) :
    run (gs++hs) w = run hs (run gs w) := by simp [run,List.foldl_append]

private theorem binary_val (o : Op) (x y : Nat) (w : List Bool) :
    val (binary o x y) w = act o (w.getD x false) (w.getD y false) :=
  row_full (Row.mk o x y .both) w

private theorem checked_bin (o : Op) (x y : Nat) :
    (binary o x y).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧
    (binary o x y).inputs.length = 2 := by cases o <;> simp [binary,gateOp]

/-- Out is a physical output-wire index. Interleaving of groups is allowed. -/
structure GateAt (C : Circuit) (n out : Nat) (o : Op) (x y : Nat) : Prop where
  layout : ∃ pre post, C.gates = pre ++ binary o x y :: post ∧ out = n+pre.length
  leftEarlier : x < out
  rightEarlier : y < out

theorem GateAt.eval {C : Circuit} {n out x y : Nat} {o : Op} (g : GateAt C n out o x y)
    (w : List Bool) (len : w.length = n) :
    (C.wires w).getD out false = act o ((C.wires w).getD x false) ((C.wires w).getD y false) := by
  obtain ⟨⟨pre,post,eq,num⟩,hx,hy⟩ := g
  let a := run pre w
  let b := a++[val (binary o x y) a]
  have la : a.length = out := by simp [a,length_run,len,num]
  have lb : b.length = out+1 := by simp [b,la]
  have res : C.wires w = run post b := by
    change run C.gates w = _
    rw [eq,appended]; rfl
  rw [res, earlier post b out (by omega), earlier post b x (by omega), earlier post b y (by omega)]
  have hx' : x < a.length := by omega
  have hy' : y < a.length := by omega
  simpa [b,←la,List.getD_eq_getElem?_getD,List.getElem?_append,hx',hy'] using binary_val o x y a

inductive Tree where
  | raw (wire : Nat)
  | external (wire : Nat)
  | join (wire : Nat) (left right : Tree)
def Tree.out : Tree → Nat | .raw i | .external i | .join i .. => i
def Tree.raws : Tree → List Nat
  | .raw i => [i] | .external _ => [] | .join _ l r => l.raws ++ r.raws
def Tree.exts : Tree → List Nat
  | .raw _ => [] | .external i => [i] | .join _ l r => l.exts ++ r.exts
def Tree.gates : Tree → List Nat
  | .raw _ | .external _ => [] | .join j l r => j::(l.gates++r.gates)
def Tree.Checked (C : Circuit) (n : Nat) : Tree → Prop
  | .raw i => i<n
  | .external _ => True
  | .join j l r => GateAt C n j .or l.out r.out ∧ l.Checked C n ∧ r.Checked C n

theorem Tree.slots (t : Tree) : t.raws.length+t.exts.length=t.gates.length+1 := by
  induction t with
  | raw i | external i => rfl
  | join j l r hl hr => simp [raws,exts,gates]; omega

theorem Tree.real {C : Circuit} {n : Nat} (t : Tree) (good : t.Checked C n)
    (w : List Bool) (hw : w.length=n) :
    let f := fun i => (C.wires w).getD i false
    f t.out = (t.raws.any f || t.exts.any f) := by
  induction t with
  | raw i => simp [out,raws,exts]
  | external i => simp [out,raws,exts]
  | join j l r hl hr =>
    obtain ⟨h,gl,gr⟩ := good
    dsimp only at hl hr ⊢
    rw [show (join j l r).out = j from rfl,h.eval w hw,hl gl,hr gr]
    simp [act,raws,exts,List.any_append,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]

private theorem anyOn {α : Type} (xs : List α) (f g : α → Bool)
    (same : ∀ j∈xs, f j = g j) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [same x (by simp),ih (fun j hj => same j (by simp [hj]))]

def chain : Nat → Nat → List Nat → List Gate × Nat
  | _,head,[] => ([],head)
  | next,head,i::xs =>
    let rest := chain (next+1) next xs
    (binary .or head i::rest.1,rest.2)

theorem chain_ok (xs : List Nat) (buf : List Bool) (h : Nat) (head : h<buf.length)
    (bounds : ∀ i ∈ xs, i<buf.length) :
    let out := chain buf.length h xs
    out.1.length = xs.length ∧ ors out.1 = xs.length ∧ Mono out.1 ∧
      out.2 < buf.length + xs.length ∧
      (run out.1 buf).getD out.2 false = (buf.getD h false || xs.any (fun j => buf.getD j false)) := by
  induction xs generalizing buf h with
  | nil => simp [chain,ors,Mono,run,head]
  | cons i xs ih =>
    let next := buf.length
    let g := binary .or h i
    let buf' := buf++[val g buf]
    have hl : buf'.length = next+1 := by simp [buf',next]
    have bound : ∀ j ∈ xs, j<buf'.length := fun j hj => by
      have hh := bounds j (by simp [hj])
      simp [buf']; omega
    have rest := ih buf' next (by rw [hl]; omega) bound
    rw [hl] at rest
    let tail := chain (next+1) next xs
    obtain ⟨len,oc,mc,lt,ok⟩ := rest
    have anyeq : xs.any (fun j => buf'.getD j false) = xs.any (fun j => buf.getD j false) := by
      apply anyOn
      intro j hj
      have old := bounds j (by simp [hj])
      simp [buf', List.getD_eq_getElem?_getD,List.getElem?_append,old]
    have add : buf'.getD next false = (buf.getD h false || buf.getD i false) := by
      rw [show buf'.getD next false = val g buf from getD_new buf _]
      exact binary_val .or h i buf
    change (g::tail.1).length = _ ∧ ors (g::tail.1) = _ ∧ Mono (g::tail.1) ∧ tail.2 < _ ∧ _
    refine ⟨by simp [tail,len],?_,?_,by simp [next,tail] at lt ⊢; omega,?_⟩
    · simpa [tail,ors,g,binary,gateOp,isOr,List.countP_cons] using oc
    · intro p hp
      rcases List.mem_cons.mp hp with eq|mem
      · exact eq ▸ checked_bin .or h i
      · exact mc p mem
    · change (run tail.1 buf').getD tail.2 false = _
      rw [show (run tail.1 buf').getD tail.2 false = _ from ok,add,anyeq]
      simp [Bool.or_assoc]

inductive Block where
  | meet (out x y : Nat)
  | group (pin : Nat) (tree : Tree)
def Block.out : Block → Nat | .meet j .. => j | .group _ t => t.out
def Block.exts : Block → List Nat | .meet _ x y => [x,y] | .group _ t => t.exts
def Block.orIDs : Block → List Nat | .meet .. => [] | .group _ t => t.gates
def Block.rawSlots : Block → Nat | .meet .. => 0 | .group _ t => t.raws.length
def Block.batch : Block → Nat | .meet .. => 0 | .group _ t => if t.raws.isEmpty then 0 else 1
def Block.Checked (C : Circuit) (n : Nat) : Block → Prop
  | .meet j x y => GateAt C n j .and x y
  | .group _ t => t.Checked C n
def Block.RealPin {α : Type} (C : Circuit) (src formal : α → List Bool) (m : Nat) : Block → Prop
  | .meet .. => True
  | .group p t => t.raws ≠ [] → p < m ∧
      ∀ a, (formal a).getD p false = t.raws.any (fun i => (C.wires (src a)).getD i false)

def blockInputs (ren : Nat → Nat) (p : Nat) (t : Tree) :=
  (if t.raws.isEmpty then [] else [p]) ++ t.exts.map ren

private theorem slots_nonempty (t : Tree) (p : Nat) (ren : Nat → Nat) :
    blockInputs ren p t ≠ [] := by
  have h := t.slots
  cases r : t.raws <;> cases e : t.exts <;> simp [blockInputs,r,e] at h ⊢

private theorem slot_price (t : Tree) (p : Nat) (ren : Nat → Nat) :
    (blockInputs ren p t).length - 1 + t.raws.length =
      t.gates.length + (if t.raws.isEmpty then 0 else 1) := by
  have h := t.slots
  have ne := slots_nonempty t p ren
  cases e : t.raws <;> simp [e,blockInputs] at h ne ⊢ <;> omega

structure Bank {α : Type} (C : Circuit) (raw formal : α → List Bool) (m : Nat) (stored : List Nat) where
  gs : List Gate
  ren : Nat → Nat
  mono : Mono gs
  bound : ∀ j ∈ stored, ren j < m+gs.length
  right : ∀ j ∈ stored, ∀ a, (run gs (formal a)).getD (ren j) false = (C.wires (raw a)).getD j false

private theorem emit {α : Type} {C : Circuit} {raw formal : α → List Bool} {n m : Nat}
    {stored : List Nat} (B : Bank C raw formal m stored) (b : Block) (src : ∀ a, (raw a).length=n)
    (dst : ∀ a, (formal a).length=m) (shape : b.Checked C n) (pins : b.RealPin C raw formal m)
    (deps : ∀ j ∈ b.exts, j ∈ stored) :
    ∃ (more : List Gate) (out : Nat), Mono more ∧
      ors more+b.rawSlots = b.orIDs.length+b.batch ∧ out<m+B.gs.length+more.length ∧
      ∀ a, (run more (run B.gs (formal a))).getD out false = (C.wires (raw a)).getD b.out false := by
  let start := m+B.gs.length
  have len a : (run B.gs (formal a)).length=start := by simp [length_run,dst,start]
  cases b with
  | meet j x y =>
    let g := binary .and (B.ren x) (B.ren y)
    refine ⟨[g],start,?_,by rfl,by simp [start],?_⟩
    · intro v hv; simp at hv; exact hv ▸ checked_bin .and _ _
    · intro a
      let buf := run B.gs (formal a)
      have hx := B.right x (deps x (by simp [Block.exts])) a
      have hy := B.right y (deps y (by simp [Block.exts])) a
      have valG : val g buf = (C.wires (raw a)).getD j false := by
        rw [shape.eval _ (src a)]
        exact (binary_val .and _ _ _).trans (congrArg₂ (act .and) hx hy)
      change (buf++[val g buf]).getD start false = _
      rw [←len a]
      exact (getD_new buf _).trans valG
  | group p t =>
    let ins := blockInputs B.ren p t
    have bound : ∀ i∈ins, i<start := by
      intro i hi
      change i ∈ (if t.raws.isEmpty then [] else [p]) ++ t.exts.map B.ren at hi
      rcases List.mem_append.mp hi with hp|he
      · cases e : t.raws with
        | nil => simp [e] at hp
        | cons x xs =>
          have pp := (pins (by simp [e])).1
          simp [e] at hp; subst i; dsimp [start]; omega
      · obtain ⟨j,hj,eq⟩ := List.mem_map.mp he
        exact eq ▸ B.bound j (deps j hj)
    have semantics a : ins.any (fun i => (run B.gs (formal a)).getD i false) =
        (C.wires (raw a)).getD t.out false := by
      have rt := t.real shape _ (src a)
      dsimp only at rt
      rw [rt]
      have ex : t.exts.any (fun j => (run B.gs (formal a)).getD (B.ren j) false) =
          t.exts.any (fun j => (C.wires (raw a)).getD j false) := by
        apply anyOn
        exact fun j hj => B.right j (deps j hj) a
      cases e : t.raws with
      | nil => simpa [ins,blockInputs,e,List.any_map,Function.comp_def] using ex
      | cons x xs =>
        obtain ⟨hb,ha⟩ := pins (by simp [e])
        have pb : p<(formal a).length := by simpa [dst] using hb
        have hv := (earlier B.gs (formal a) p pb).trans (ha a)
        have eqin : ins = p::t.exts.map B.ren := by simp [ins,blockInputs,e]
        rw [eqin,List.any_cons,List.any_map]
        simpa only [e,Function.comp_def] using congrArg₂ (· || ·) hv ex
    cases eq : ins with
    | nil => exact False.elim ((slots_nonempty t p B.ren) eq)
    | cons h xs =>
      have bh : h<start := bound h (by simp [eq])
      have bx : ∀ i∈xs,i<start := fun i hi => bound i (by simp [eq,hi])
      have dummy := chain_ok xs (List.replicate start false) h (by simpa using bh) (by simpa using bx)
      simp only [List.length_replicate] at dummy
      obtain ⟨ln,oc,mono,lt,_⟩ := dummy
      refine ⟨(chain start h xs).1,(chain start h xs).2,mono,?_,by simpa [ln,start] using lt,?_⟩
      · have cost := slot_price t p B.ren
        change ins.length - 1 + _ = _ at cost
        simpa [eq,oc,Block.rawSlots,Block.orIDs,Block.batch] using cost
      · intro a
        have hbuf := chain_ok xs (run B.gs (formal a)) h (by simpa [len] using bh) (by simpa [len] using bx)
        rw [len] at hbuf
        exact hbuf.2.2.2.2.trans (by simpa [eq,Block.out] using semantics a)

def Book (C : Circuit) (n : Nat) : List Nat → List Block → Prop
  | _,[] => True
  | seen,b::bs => b.Checked C n ∧ (∀ j∈b.exts,j∈seen) ∧ Book C n (b.out::seen) bs
def allGates (bs : List Block) := bs.flatMap Block.orIDs
def rawCount (bs : List Block) := (bs.map Block.rawSlots).sum
def batchCount (bs : List Block) := (bs.map Block.batch).sum
def outputs : List Block → List Nat → List Nat
  | [],stored => stored
  | b::bs,stored => outputs bs (b.out::stored)

private theorem compile_book {α : Type} {C : Circuit} {raw formal : α → List Bool} {n m : Nat}
    (src : ∀ a, (raw a).length=n) (dst : ∀ a, (formal a).length=m) (bs : List Block)
    (stored : List Nat) (state : Bank C raw formal m stored)
    (book : Book C n stored bs) (pins : ∀ b∈bs,b.RealPin C raw formal m) :
    ∃ B : Bank C raw formal m (outputs bs stored),
      ors B.gs + rawCount bs = ors state.gs + (allGates bs).length + batchCount bs := by
  induction bs generalizing stored with
  | nil => exact ⟨state,by simp [rawCount,batchCount,allGates]⟩
  | cons b bs ih =>
    obtain ⟨shape,deps,book⟩ := book
    obtain ⟨more,out,mono,cost,bound,right⟩ := emit state b src dst shape (pins b (by simp)) deps
    let gs := state.gs ++ more
    let ren := fun i => if i=b.out then out else state.ren i
    let B : Bank C raw formal m (b.out::stored) := {
      gs := gs
      ren := ren
      mono := by
        intro g hg
        exact (List.mem_append.mp hg).elim (state.mono g) (mono g)
      bound := by
        intro j hj
        by_cases eq : j=b.out
        · simpa [ren,gs,eq,Nat.add_assoc] using bound
        · have old := state.bound j (by simpa [eq] using hj)
          simp [ren,gs,eq]; omega
      right := by
        intro j hj a
        by_cases eq : j=b.out
        · simpa [ren,gs,eq,appended] using right a
        · have old : j∈stored := by simpa [eq] using hj
          have small := state.bound j old
          have cut : state.ren j < (run state.gs (formal a)).length := by simpa [length_run,dst] using small
          exact (show (run gs (formal a)).getD (ren j) false = _ from by
            rw [show ren j = state.ren j from by simp [ren,eq],show run gs (formal a) = _ from appended state.gs more (formal a),earlier more _ _ cut]).trans (state.right j old a)
    }
    obtain ⟨result,eq⟩ := ih (b.out::stored) B book (fun x hx => pins x (by simp [hx]))
    have oc : ors B.gs = ors state.gs + ors more := by simp [B,gs,ors,List.countP_append]
    refine ⟨result,?_⟩
    change ors result.gs + _ = _
    simp only [allGates,List.flatMap_cons,List.length_append,rawCount,batchCount,List.map_cons,List.sum_cons]
    change ors result.gs + (b.rawSlots + rawCount bs) =
      ors state.gs + (b.orIDs.length + (allGates bs).length) + (b.batch + batchCount bs)
    omega
def idsFrom : Nat → List Gate → List Nat
  | _,[] => []
  | n,g::gs => if isOr g then n :: idsFrom (n+1) gs else idsFrom (n+1) gs

private theorem ids_append (xs ys : List Gate) (n : Nat) :
    idsFrom n (xs++ys) = idsFrom n xs ++ idsFrom (n+xs.length) ys := by
  induction xs generalizing n with
  | nil => simp [idsFrom]
  | cons g xs ih =>
    cases e : isOr g <;> simp [idsFrom,e,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem ids_len (gs : List Gate) (n : Nat) : (idsFrom n gs).length = ors gs := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => cases e : isOr g <;> simp [idsFrom,e,ors,List.countP_cons,ih,ors] at *

private theorem or_in_ids {C : Circuit} {n j x y : Nat} (h : GateAt C n j .or x y) :
    j ∈ idsFrom n C.gates := by
  obtain ⟨⟨pre,post,eq,rfl⟩,_,_⟩ := h
  rw [eq,ids_append]; exact List.mem_append_right _ (by simp [idsFrom,isOr,binary,gateOp])

private theorem tree_ids {C : Circuit} {n : Nat} (t : Tree) (h : t.Checked C n) :
    ∀ j∈t.gates,j∈idsFrom n C.gates := by
  induction t with
  | raw | external => simp [Tree.gates]
  | join j l r hl hr =>
    intro i hi
    rcases List.mem_cons.mp hi with eq|lr
    · exact eq ▸ or_in_ids h.1
    · exact (List.mem_append.mp lr).elim (hl h.2.1 i) (hr h.2.2 i)

private theorem book_ids {C : Circuit} {n : Nat} (bs : List Block) (stored : List Nat) (h : Book C n stored bs) :
    ∀ j∈allGates bs,j∈idsFrom n C.gates := by
  induction bs generalizing stored with
  | nil => simp [allGates]
  | cons b bs ih =>
    intro i hi
    rcases List.mem_append.mp hi with own|rest
    · cases b with
      | meet => simp [Block.orIDs] at own
      | group p t => exact tree_ids t h.1 i own
    · exact ih _ h.2.2 i rest

theorem count_of_disjoint {C : Circuit} {n : Nat} (bs : List Block) (book : Book C n [] bs)
    (privateSlots : (allGates bs).Nodup) : (allGates bs).length ≤ ors C.gates := by
  have sub : (allGates bs).toFinset ⊆ (idsFrom n C.gates).toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (book_ids bs [] book x (List.mem_toFinset.mp hx))
  rw [← List.toFinset_card_of_nodup privateSlots,←ids_len C.gates n]
  exact (Finset.card_le_card sub).trans (List.toFinset_card_le _)

/-- Semantic gate saving in the physically indexed original and compiled D. -/
theorem abstract_groups {α : Type} {C : Circuit} (raw formal : α → List Bool) (n m : Nat)
    (src : ∀ a, (raw a).length=n) (dst : ∀ a, (formal a).length=m) (bs : List Block)
    (book : Book C n [] bs) (pins : ∀ b∈bs,b.RealPin C raw formal m)
    (out : C.output ∈ outputs bs []) (privateSlots : (allGates bs).Nodup) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a, D.eval (formal a) = C.eval (raw a)) ∧
      ors D.gates + rawCount bs = (allGates bs).length + batchCount bs ∧
      ors D.gates + rawCount bs ≤ ors C.gates + batchCount bs := by
  let init : Bank C raw formal m [] := ⟨[],id,by simp [Mono],by simp,by simp⟩
  obtain ⟨B,eq⟩ := compile_book src dst bs [] init book pins
  have x : ors B.gs + rawCount bs = (allGates bs).length + batchCount bs := by
    simpa [init,ors] using eq
  exact ⟨⟨B.gs,B.ren C.output⟩,fun g hg => ⟨(B.mono g hg).1,(B.mono g hg).2.le⟩,
    B.right C.output out,x,x.le.trans (Nat.add_le_add_right (count_of_disjoint bs book privateSlots) _)⟩

/-- Actual endpoint input list: one bit per group, the OR of that group's raw
input bits. Duplicate raw occurrences are harmless and remain separately counted. -/
def incidence (groups : List (List Nat)) (w : List Bool) :=
  groups.map (fun indices => indices.any (fun i => w.getD i false))

theorem pin_real_of_lookup {α : Type} {C : Circuit} {n : Nat} (src : α → List Bool)
    (arity : ∀ a, (src a).length=n) (groups : List (List Nat)) (p : Nat) (t : Tree)
    (shape : t.Checked C n) (lookup : groups[p]? = some t.raws) :
    (Block.group p t).RealPin C src (fun a => incidence groups (src a)) groups.length := by
  have small : ∀ j∈t.raws, j<n := by
    clear lookup
    induction t with
    | raw i => simpa [Tree.raws,Tree.Checked] using shape
    | external i => simp [Tree.raws]
    | join i l r hl hr =>
      intro j hj
      exact (List.mem_append.mp hj).elim (hl shape.2.1 j) (hr shape.2.2 j)
  intro _
  have lt : p < groups.length := by
    by_contra! large
    simp [List.getElem?_eq_none large] at lookup
  refine ⟨lt,fun a => ?_⟩
  have hh : ∀ j∈t.raws, (src a).getD j false = (C.wires (src a)).getD j false :=
    fun j hj => (earlier C.gates (src a) j (by simpa [arity] using small j hj)).symm
  simpa [incidence,List.getD_eq_getElem?_getD,List.getElem?_map,lookup] using anyOn t.raws _ _ hh

#print axioms abstract_groups
#print axioms pin_real_of_lookup
end ThresholdOrGroups
