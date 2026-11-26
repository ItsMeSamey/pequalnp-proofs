import ThresholdFactorNetwork
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
open ThresholdFactorExpr ThresholdFactorRecipe ThresholdFactorNetwork ThresholdUniqueRaw
namespace ThresholdFactorForest

def treeTerm : Tree → Term
  | .raw i => .raw i
  | .external j => .ref j
  | .join _ l r => .node .or (treeTerm l) (treeTerm r)

def ordinary : Block → Term
  | .meet _ x y => .node .and (.ref x) (.ref y)
  | .group _ t => treeTerm t

def target (x z : Nat) (a b : Tree) (g : Block) :=
  if g.out=a.out ∨ g.out=b.out then Term.raw x
  else if g.out=z then factored x a b else ordinary g

def job (x z : Nat) (a b : Tree) (g : Block) : Job := ⟨g.out,target x z a b g⟩

theorem tree_cost (t : Tree) : (treeTerm t).cost=t.gates.length := by
  induction t with
  | raw | external => rfl
  | join j l r hl hr => simp [treeTerm,Tree.gates,Term.cost,hl,hr]

theorem ordinary_cost (g : Block) : (ordinary g).cost=charge g := by
  cases g with
  | meet => rfl
  | group p t => exact tree_cost t

private theorem earlier (gs : List Gate) (w : List Bool) (i : Nat) (lt : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append,lt]

private theorem realize_tree {C : Circuit} {n} (t : Tree) (shape : t.Checked C n) (w : List Bool)
    (arity : w.length=n) (S : Nat → Bool) (ext : ∀ j∈t.exts,S j=(C.wires w).getD j false) :
    (treeTerm t).value (fun i => w.getD i false) S=(C.wires w).getD t.out false := by
  induction t with
  | raw i =>
    exact (earlier C.gates w i (by simpa [arity,Tree.Checked] using shape)).symm
  | external i => exact ext i (by simp [Tree.exts])
  | join j l r hl hr =>
    change _=(C.wires w).getD j false
    rw [shape.1.eval w arity]
    exact congrArg₂ (act .or) (hl shape.2.1 (fun i hi => ext i (by simp [Tree.exts,hi])))
      (hr shape.2.2 (fun i hi => ext i (by simp [Tree.exts,hi])))

def adjusted (a b : Tree) (x : Nat) (C : Circuit) (w : List Bool) (j : Nat) :=
  if j=a.out ∨ j=b.out then w.getD x false else (C.wires w).getD j false

private theorem ref_agrees (a b : Tree) (x : Nat) (C : Circuit) (w : List Bool)
    (g : Block) (safe : ∀ j∈g.exts,j≠a.out ∧ j≠b.out) :
    ∀ j∈g.exts, adjusted a b x C w j=(C.wires w).getD j false := by
  intro j hj
  simp [adjusted,(safe j hj).1,(safe j hj).2]

theorem ordinary_real {C : Circuit} {n} (g : Block) (checked : g.Checked C n) (w : List Bool)
    (arity : w.length=n) (S : Nat → Bool) (ext : ∀ j∈g.exts,S j=(C.wires w).getD j false) :
    (ordinary g).value (fun i => w.getD i false) S=(C.wires w).getD g.out false := by
  cases g with
  | meet j l r =>
    change _=(C.wires w).getD j false
    rw [checked.eval w arity]
    exact congrArg₂ (act .and) (ext l (by simp [Block.exts])) (ext r (by simp [Block.exts]))
  | group p t => exact realize_tree t checked w arity S ext

private theorem flatten (t : Tree) (R S : Nat → Bool) :
    (treeTerm t).value R S=(t.raws.any R || t.exts.any S) := by
  induction t with
  | raw i => simp [treeTerm,Term.value,Tree.raws,Tree.exts]
  | external i => simp [treeTerm,Term.value,Tree.raws,Tree.exts]
  | join j l r hl hr =>
    simp [treeTerm,Term.value,act,Tree.raws,Tree.exts,hl,hr,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]

structure Cut (C : Circuit) (n x z : Nat) (a b : Tree) (bs : List Block) : Prop where
  raw : x<n
  left : a.Checked C n
  right : b.Checked C n
  inLeft : x∈a.raws
  inRight : x∈b.raws
  distinct : a.out≠b.out
  leftNotMeet : a.out≠z
  rightNotMeet : b.out≠z
  unobserved : C.output≠a.out ∧ C.output≠b.out
  receiver : GateAt C n z .and a.out b.out
  exclusive : ∀ g∈bs,g.out≠z → ∀ j∈g.exts,j≠a.out ∧ j≠b.out
  leftIn : ∃ p,Block.group p a∈bs
  rightIn : ∃ p,Block.group p b∈bs
  meetIn : Block.meet z a.out b.out∈bs
  distinctOutputs : (bs.map Block.out).Nodup

theorem job_real {C : Circuit} {n x z : Nat} {a b : Tree} {bs : List Block}
    (cut : Cut C n x z a b bs) (g : Block) (mem : g∈bs) (shape : g.Checked C n)
    (w : List Bool) (arity : w.length=n) :
    (job x z a b g).term.value (fun i => w.getD i false) (adjusted a b x C w) =
      adjusted a b x C w g.out := by
  let S := adjusted a b x C w
  by_cases priv : g.out=a.out ∨ g.out=b.out
  · simp [job,target,adjusted,priv,Term.value]
  by_cases isMeet : g.out=z
  · obtain ⟨p,la⟩ := cut.leftIn
    obtain ⟨q,rb⟩ := cut.rightIn
    have gl := ordinary_real (.group p a) cut.left w arity S
      (ref_agrees a b x C w _ (cut.exclusive _ la cut.leftNotMeet))
    have gr := ordinary_real (.group q b) cut.right w arity S
      (ref_agrees a b x C w _ (cut.exclusive _ rb cut.rightNotMeet))
    change (treeTerm a).value _ S=_ at gl
    change (treeTerm b).value _ S=_ at gr
    rw [flatten] at gl gr
    simp only [job,target,if_neg priv,if_pos isMeet]
    rw [factor_sem _ _ _ _ _ cut.inLeft cut.inRight,gl,gr]
    rw [adjusted,if_neg priv,isMeet,cut.receiver.eval w arity]
    rfl
  · simp only [job,target,if_neg priv,if_neg isMeet]
    rw [adjusted,if_neg priv]
    exact ordinary_real g shape w arity S (ref_agrees a b x C w g (cut.exclusive g mem isMeet))

theorem total_price {C : Circuit} {n x z : Nat} {a b : Tree} {bs : List Block}
    (cut : Cut C n x z a b bs) :
    (bs.map (fun g => (target x z a b g).cost)).sum+1≤(bs.map charge).sum := by
  classical
  obtain ⟨p,ha⟩ := cut.leftIn
  obtain ⟨q,hb⟩ := cut.rightIn
  let A := Block.group p a
  let B := Block.group q b
  let Z := Block.meet z a.out b.out
  have first : bs.Perm (A::bs.erase A) := List.perm_cons_erase ha
  have rB : B∈bs.erase A := by
    have mem := first.mem_iff.mp hb
    rcases List.mem_cons.mp mem with eq|ok
    · exact False.elim (cut.distinct (congrArg Block.out eq.symm))
    · exact ok
  have second := List.perm_cons_erase rB
  have ab := first.trans (second.cons A)
  have rZ : Z∈(bs.erase A).erase B := by
    have mem := ab.mem_iff.mp cut.meetIn
    simpa [A,B,Z] using mem
  let rest := ((bs.erase A).erase B).erase Z
  have perm : bs.Perm (A::B::Z::rest) := ab.trans (((List.perm_cons_erase rZ).cons B).cons A)
  have nd := ((perm.map Block.out).nodup_iff).mp cut.distinctOutputs
  simp only [List.map_cons,List.nodup_cons] at nd
  have same : ∀ g∈rest,(target x z a b g).cost=charge g := by
    intro g hg
    have mem : g.out ∈ rest.map Block.out := List.mem_map.mpr (show ∃ j∈rest,j.out=g.out from ⟨g,hg,rfl⟩)
    have l : g.out≠a.out := fun eq => nd.1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (show A.out∈rest.map Block.out from by change a.out∈_; rw [←eq];exact mem)))
    have r : g.out≠b.out := fun eq => nd.2.1 (List.mem_cons_of_mem _ (show B.out∈rest.map Block.out from by change b.out∈_; rw [←eq];exact mem))
    have zi : g.out≠z := fun eq => nd.2.2.1 (by change z∈_; rw [←eq];exact mem)
    simp [target,l,r,zi,ordinary_cost]
  have tail := List.map_congr_left same
  rw [(perm.map _).sum_eq,(perm.map charge).sum_eq]
  simp only [List.map_cons,List.sum_cons,tail]
  simp [target,A,B,Z,Block.out,charge,Term.cost,Ne.symm cut.distinct,cut.leftNotMeet,
    cut.rightNotMeet,Ne.symm cut.leftNotMeet,Ne.symm cut.rightNotMeet]
  have price := factor_cost x a b cut.inLeft cut.inRight
  omega

private theorem outputs_eq (x z : Nat) (a b : Tree) (bs : List Block) (seen : List Nat) :
    seenAfter (bs.map (job x z a b)) seen=outputs bs seen := by
  induction bs generalizing seen with
  | nil => rfl
  | cons g gs ih => exact ih (g.out::seen)

theorem actual_saving {C : Circuit} {n x z : Nat} (L : Layout C n) (pin : T2OrPartition.Id C → Nat)
    (a b : Tree) (cut : Cut C n x z a b (forest L pin))
    (obs : ∃ i : T2OrPartition.Id C,C.output=n+i.val)
    (ready : valid n [] ((forest L pin).map (job x z a b))) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size+1≤C.size ∧
      ∀ w : List Bool,w.length=n → D.eval w=C.eval w := by
  let bs := forest L pin
  let raw := fun a : {w : List Bool // w.length=n} => a.val
  let spec := fun w : {w : List Bool // w.length=n} => adjusted a b x C w.val
  let init : Work n raw spec [] := ⟨[],id,by simp [Mono],by simp,by simp⟩
  obtain ⟨W,sz⟩ := program (fun w => w.property) _ [] init ready (by
    intro j mem w
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp mem
    exact job_real cut g hg (forest_checked L pin g hg) w.val w.property)
  obtain ⟨i,hi⟩ := obs
  have seen := observed_root L pin i hi
  rw [←outputs_eq x z a b] at seen
  refine ⟨⟨W.gs,W.ren C.output⟩,fun g hg => ⟨(W.mono g hg).1,(W.mono g hg).2.le⟩,?_,?_⟩
  · have bound := forest_charge L pin
    have price := total_price cut
    simp [init,List.map_map,Function.comp_def,job] at sz
    change W.gs.length+1≤C.size
    omega
  · intro w len
    have ok := W.correct C.output seen ⟨w,len⟩
    change (run W.gs w).getD (W.ren C.output) false=C.eval w
    simpa [raw,spec,adjusted,cut.unobserved.1,cut.unobserved.2,Circuit.eval] using ok
end ThresholdFactorForest
