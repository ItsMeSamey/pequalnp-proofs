import ThresholdOrPhysicalBook
import T2BenchmarkNormalize
import Mathlib.Data.List.Dedup
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
namespace ThresholdUniqueRaw
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

private theorem anyOn {α : Type} (xs : List α) (f g : α → Bool)
    (same : ∀ j∈xs, f j = g j) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [same x (by simp),ih (fun j hj => same j (by simp [hj]))]


def repeats : Block → Nat
  | .meet .. => 0
  | .group _ t => t.raws.length-t.raws.dedup.length

def charge : Block → Nat
  | .meet .. => 1
  | .group _ t => t.gates.length

def ports (ren : Nat → Nat) (t : Tree) := t.raws.dedup ++ t.exts.map ren

private theorem rawBound {C : Circuit} {n : Nat} (t : Tree) (shape : t.Checked C n) :
    ∀ j∈t.raws,j<n := by
  induction t with
  | raw i => simpa [Tree.raws,Tree.Checked] using shape
  | external i => simp [Tree.raws]
  | join i l r hl hr =>
    intro j hj
    exact (List.mem_append.mp hj).elim (hl shape.2.1 j) (hr shape.2.2 j)

private theorem emit {α : Type} {C : Circuit} {raw : α → List Bool} {n : Nat}
    {stored : List Nat} (B : Bank C raw raw n stored) (b : Block)
    (src : ∀ a,(raw a).length=n) (shape : b.Checked C n) (deps : ∀ j∈b.exts,j∈stored) :
    ∃ (more : List Gate) (out : Nat), Mono more ∧
      more.length+repeats b=charge b ∧ out<n+B.gs.length+more.length ∧
      ∀ a,(run more (run B.gs (raw a))).getD out false=(C.wires (raw a)).getD b.out false := by
  let start := n+B.gs.length
  have len a : (run B.gs (raw a)).length=start := by simp [length_run,src,start]
  cases b with
  | meet j x y =>
    let g := binary .and (B.ren x) (B.ren y)
    refine ⟨[g],start,?_,by rfl,by simp [start],?_⟩
    · intro v hv; simp at hv; exact hv ▸ checked_bin .and _ _
    · intro a
      let buf := run B.gs (raw a)
      have hx := B.right x (deps x (by simp [Block.exts])) a
      have hy := B.right y (deps y (by simp [Block.exts])) a
      have valG : val g buf = (C.wires (raw a)).getD j false := by
        rw [shape.eval _ (src a)]
        exact (binary_val .and _ _ _).trans (congrArg₂ (act .and) hx hy)
      change (buf++[val g buf]).getD start false = _
      rw [←len a]
      exact (getD_new buf _).trans valG
  | group p t =>
    let ins := ports B.ren t
    have bound : ∀ i∈ins,i<start := by
      intro i hi
      rcases List.mem_append.mp hi with old|ext
      · have small := rawBound t shape i (List.mem_dedup.mp old)
        dsimp [start]; omega
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ext
        exact B.bound j (deps j hj)
    have semantics a : ins.any (fun i => (run B.gs (raw a)).getD i false) =
        (C.wires (raw a)).getD t.out false := by
      have rt := t.real shape _ (src a)
      dsimp only at rt
      rw [rt]
      change (t.raws.dedup ++ t.exts.map B.ren).any _ = _
      rw [List.any_append,List.any_map]
      apply congrArg₂ (· || ·)
      · have agrees : ∀ j∈t.raws.dedup,(run B.gs (raw a)).getD j false=(C.wires (raw a)).getD j false := by
          intro j hj
          have lt : j<(raw a).length := by rw [src]; exact rawBound t shape j (List.mem_dedup.mp hj)
          exact (earlier _ _ _ lt).trans (earlier C.gates _ _ lt).symm
        rw [anyOn _ _ _ agrees]
        apply Bool.eq_iff_iff.mpr
        simp [List.any_eq_true]
      · exact anyOn _ _ _ (fun j hj => B.right j (deps j hj) a)
    have ne : ins≠[] := by
      intro eq
      have z : t.raws.dedup=[] ∧ t.exts=[] := by simpa [ins,ports] using eq
      have zr : t.raws=[] := by simpa using z.1
      have impossible := t.slots
      simp [zr,z.2] at impossible
    cases eq : ins with
    | nil => exact False.elim (ne eq)
    | cons h xs =>
      have bh : h<start := bound h (by simp [eq])
      have bx : ∀ i∈xs,i<start := fun i hi => bound i (by simp [eq,hi])
      have dummy := chain_ok xs (List.replicate start false) h (by simpa using bh) (by simpa using bx)
      simp only [List.length_replicate] at dummy
      obtain ⟨ln,_,mono,lt,_⟩ := dummy
      refine ⟨(chain start h xs).1,(chain start h xs).2,mono,?_,by simpa [ln,start] using lt,?_⟩
      · have slots := t.slots
        have leq := t.raws.dedup_sublist.length_le
        have sz := congrArg List.length eq
        simp only [ins,ports,List.length_append,List.length_map,List.length_cons] at sz
        change (chain start h xs).1.length + (t.raws.length-t.raws.dedup.length)=t.gates.length
        omega
      · intro a
        have hbuf := chain_ok xs (run B.gs (raw a)) h (by simpa [len] using bh) (by simpa [len] using bx)
        rw [len] at hbuf
        exact hbuf.2.2.2.2.trans (by simpa [eq,Block.out] using semantics a)

private theorem compile {α : Type} {C : Circuit} {raw : α → List Bool} {n : Nat}
    (src : ∀ a,(raw a).length=n) (bs : List Block) (stored : List Nat)
    (state : Bank C raw raw n stored) (book : Book C n stored bs) :
    ∃ B : Bank C raw raw n (outputs bs stored),
      B.gs.length+(bs.map repeats).sum=state.gs.length+(bs.map charge).sum := by
  induction bs generalizing stored with
  | nil => exact ⟨state,by simp⟩
  | cons b bs ih =>
    obtain ⟨shape,deps,book⟩ := book
    obtain ⟨more,out,mono,cost,bound,right⟩ := emit state b src shape deps
    let gs := state.gs ++ more
    let ren := fun i => if i=b.out then out else state.ren i
    let B : Bank C raw raw n (b.out::stored) := {
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
          have cut : state.ren j < (run state.gs (raw a)).length := by simpa [length_run,src] using small
          exact (show (run gs (raw a)).getD (ren j) false = _ from by
            rw [show ren j = state.ren j from by simp [ren,eq],show run gs (raw a) = _ from appended state.gs more (raw a),earlier more _ _ cut]).trans (state.right j old a)
    }
    obtain ⟨result,eq⟩ := ih (b.out::stored) B book
    refine ⟨result,?_⟩
    have rows : B.gs.length=state.gs.length+more.length := by simp [B,gs]
    simp only [List.map_cons,List.sum_cons]; omega

theorem dedup_book {α : Type} {C : Circuit} {n : Nat} (raw : α → List Bool)
    (arity : ∀ a,(raw a).length=n) (bs : List Block) (book : Book C n [] bs)
    (seen : C.output∈outputs bs []) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a,D.eval (raw a)=C.eval (raw a)) ∧
      D.size+(bs.map repeats).sum=(bs.map charge).sum := by
  let init : Bank C raw raw n [] := ⟨[],id,by simp [Mono],by simp,by simp⟩
  obtain ⟨B,sz⟩ := compile arity bs [] init book
  exact ⟨⟨B.gs,B.ren C.output⟩,fun g hg => ⟨(B.mono g hg).1,(B.mono g hg).2.le⟩,
    B.right C.output seen,by simpa [init,Circuit.size] using sz⟩

private def meetTag : Block → Bool | .meet .. => true | .group .. => false

private theorem charges (bs : List Block) :
    (bs.map charge).sum=(allGates bs).length+(bs.filter meetTag).length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;>
      simp [allGates,List.flatMap_cons,Block.orIDs,charge,meetTag,List.filter_cons] at ih ⊢ <;> omega

theorem forest_charge {C : Circuit} {n : Nat} (L : Layout C n) (pin : T2OrPartition.Id C → Nat) :
    ((forest L pin).map charge).sum≤C.size := by
  let xs := List.finRange C.gates.length
  let fixedPred := fun i : T2OrPartition.Id C => (T2OrPartition.next C n i).isNone
  let orPred := fun i => decide (L.op i=Op.or)
  have tag (i : T2OrPartition.Id C) : meetTag (makeBlock L pin i)= !(orPred i) := by
    unfold makeBlock
    split <;> simp_all [orPred,meetTag]
  have upper (ys : List (T2OrPartition.Id C)) :
      (ys.filter orPred).length+
        (((ys.filter fixedPred).map (makeBlock L pin)).filter meetTag).length ≤ ys.length := by
    induction ys with
    | nil => simp
    | cons i ys ih =>
      cases k : fixedPred i <;> cases o : orPred i <;>
        simp [List.filter_cons,k,o,tag] at * <;> omega
  rw [charges,(ids_permute L pin).length_eq]
  simpa only [orIndex,List.length_map,forest,fixed,xs,fixedPred,orPred,List.length_finRange,
    Circuit.size] using upper xs

theorem forest_saved {C : Circuit} {n : Nat} (L : Layout C n) (pin : T2OrPartition.Id C → Nat)
    (internal : MeetsInternal L) (obs : ∃ i : T2OrPartition.Id C,C.output=n+i.val)
    {α : Type} (raw : α → List Bool) (arity : ∀ a,(raw a).length=n) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a,D.eval (raw a)=C.eval (raw a)) ∧
      D.size+((forest L pin).map repeats).sum ≤ C.size := by
  obtain ⟨i,hi⟩ := obs
  obtain ⟨D,mono,sem,cost⟩ := dedup_book raw arity _ (extracted_book L internal pin)
    (observed_root L pin i hi)
  exact ⟨D,mono,sem,cost.le.trans (forest_charge L pin)⟩

theorem group_raw_nodup {C : Circuit} {n : Nat} (L : Layout C n) (pin : T2OrPartition.Id C → Nat)
    (internal : MeetsInternal L) (hn : 2≤n) (mini : T2SoleOrSplice.LexMinimum n C)
    {p : Nat} {t : Tree} (member : Block.group p t∈forest L pin) : t.raws.Nodup := by
  obtain ⟨D,mono,sem,cost⟩ := forest_saved L pin internal (T2BenchmarkNormalize.output_internal mini.eligible)
    (T2SoleOrSplice.vector (n:=n)) (fun _ => by simp [T2SoleOrSplice.vector])
  have computes : T2SoleOrSplice.Computes n D := by
    intro s; rw [sem]; exact mini.eligible.1 s
  obtain ⟨E,eligible,smaller⟩ := T2BenchmarkNormalize.canNormalize hn D mono computes
  have cmp := mini.primary E eligible
  have zero : ((forest L pin).map repeats).sum=0 := by omega
  have vanish := List.sum_eq_zero_iff_forall_eq_nat.mp zero _ (List.mem_map.mpr ⟨_,member,rfl⟩)
  apply List.nodup_iff_le_length_dedup.mpr
  change t.raws.length-t.raws.dedup.length=0 at vanish
  omega

#print axioms forest_saved
#print axioms group_raw_nodup
end ThresholdUniqueRaw
