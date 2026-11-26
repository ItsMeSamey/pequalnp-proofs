import ThresholdSharedPairErase
import ThresholdFactorCut
import ThresholdRegularSource
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
  ThresholdFactorExpr ThresholdFactorRecipe ThresholdFactorNetwork ThresholdFactorForest
  ThresholdUniqueRaw T2OrPartition ThresholdSharedFlow ThresholdSharedPairErase
namespace ThresholdSharedPairMinimum
private theorem flatten (t : Tree) (R S : Nat → Bool) :
    (treeTerm t).value R S=(t.raws.any R || t.exts.any S) := by
  induction t with
  | raw i => simp [treeTerm,Term.value,Tree.raws,Tree.exts]
  | external i => simp [treeTerm,Term.value,Tree.raws,Tree.exts]
  | join j l r hl hr =>
    simp [treeTerm,Term.value,act,Tree.raws,Tree.exts,hl,hr,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]

private theorem treeAvail {C : Circuit} {n} (t : Tree) (seen : List Nat)
    (checked : t.Checked C n) (refs : ∀ j∈t.exts,j∈seen) : (treeTerm t).Avail n seen := by
  induction t with
  | raw i => exact checked
  | external i => exact refs i (by simp [Tree.exts])
  | join j l r hl hr =>
    exact ⟨hl checked.2.1 (fun i hi => refs i (by simp [Tree.exts,hi])),
      hr checked.2.2 (fun i hi => refs i (by simp [Tree.exts,hi]))⟩

private theorem rawBound {C : Circuit} {n : Nat} (t : Tree) (shape : t.Checked C n) :
    ∀ j∈t.raws,j<n := by
  induction t with
  | raw i => simpa [Tree.raws,Tree.Checked] using shape
  | external i => simp [Tree.raws]
  | join i l r hl hr =>
    intro j hj
    exact (List.mem_append.mp hj).elim (hl shape.2.1 j) (hr shape.2.2 j)

private theorem distinct_parts (bs : List Block) (A B : Block) (ne : A≠B) (a : A∈bs) (b : B∈bs)
    (w : Nat) (ha : w∈A.orIDs) (hb : w∈B.orIDs) : 2≤(allGates bs).count w := by
  have one (ds : List Block) (D : Block) (hd : D∈ds) (hw : w∈D.orIDs) :
      0<(allGates ds).count w := List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨D,hd,hw⟩)
  induction bs with
  | nil => simp at a
  | cons c cs ih =>
    change 2≤(c.orIDs++allGates cs).count w
    rw [List.count_append]
    rcases List.mem_cons.mp a with ac|ac
    · subst c
      have bt := (List.mem_cons.mp b).resolve_left (Ne.symm ne)
      have h1 := List.count_pos_iff.mpr ha
      have h2 := one cs B bt hb
      omega
    · rcases List.mem_cons.mp b with bc|bc
      · subst c
        have h1 := List.count_pos_iff.mpr hb
        have h2 := one cs A ac ha
        omega
      · have := ih ac bc
        omega

private noncomputable def replace (B : Block) (q : Term) (g : Block) : Job := by
  classical
  exact ⟨g.out,if g=B then q else ordinary g⟩

private theorem out_replace (B : Block) (q : Term) (ds : List Block) (seen : List Nat) :
    seenAfter (ds.map (replace B q)) seen=outputs ds seen := by
  induction ds generalizing seen with
  | nil => rfl
  | cons g gs ih => exact ih (g.out::seen)

private theorem save {C : Circuit} {n} (L : Layout C n) (pin : Id C → Nat) (internal : MeetsInternal L)
    (B : Block) (q : Term) (included : B∈forest L pin) (price : q.cost+1=charge B)
    (available : ∀ seen : List Nat,(∀ j∈B.exts,j∈seen) → q.Avail n seen)
    (sem : ∀ w : List Bool,w.length=n →
      q.value (fun i => w.getD i false) (fun i => (C.wires w).getD i false)=(C.wires w).getD B.out false)
    (obs : ∃ i : Id C,C.output=n+i.val) :
    ∃ D : Circuit,PEqualNP.MetaComplexity.Monotone2 D ∧ D.size+1≤C.size ∧
      ∀ w : List Bool,w.length=n → D.eval w=C.eval w := by
  classical
  let bs := forest L pin
  let f := replace B q
  have ready (ds : List Block) (seen : List Nat) (book : Book C n seen ds) :
      valid n seen (ds.map f) := by
    induction ds generalizing seen with
    | nil => trivial
    | cons g gs ih =>
      obtain ⟨shape,refs,tail⟩ := book
      refine ⟨?_,ih (g.out::seen) tail⟩
      by_cases eq : g=B
      · subst g; simpa [f,replace] using available seen refs
      · simp only [f,replace,if_neg eq]
        cases g with
        | meet j l r => exact ⟨refs l (by simp [Block.exts]),refs r (by simp [Block.exts])⟩
        | group p t => exact treeAvail t seen shape refs
  let raw := fun w : {w : List Bool // w.length=n} => w.val
  let spec := fun w : {w : List Bool // w.length=n} => fun i => (C.wires w.val).getD i false
  let init : Work n raw spec [] := ⟨[],id,by simp [Mono],by simp,by simp⟩
  obtain ⟨F,cost⟩ := program (fun w => w.property) (bs.map f) [] init
    (ready _ _ (extracted_book L internal pin)) (by
      intro j hj w
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hj
      by_cases eq : g=B
      · subst g; simpa [f,replace,spec,raw] using sem w.val w.property
      · simpa [f,replace,eq,spec,raw] using ordinary_real g (forest_checked L pin g hg) w.val w.property
          (fun i => (C.wires w.val).getD i false) (fun _ _ => rfl))
  have calcCost (ds : List Block) :
      (ds.map (fun g => (f g).term.cost)).sum + ds.count B = (ds.map charge).sum := by
    induction ds with
    | nil => simp
    | cons g gs ih =>
      by_cases eq : g=B
      · subst g; simp [List.count_cons,f,replace] at * <;> omega
      · have rev : B≠g := Ne.symm eq
        simp [List.count_cons,f,replace,eq,rev,ordinary_cost] at * <;> omega
  have positive : 0<bs.count B := List.count_pos_iff.mpr included
  obtain ⟨i,hi⟩ := obs
  have seen := observed_root L pin i hi
  rw [←out_replace B q] at seen
  refine ⟨⟨F.gs,F.ren C.output⟩,fun g hg => ⟨(F.mono g hg).1,(F.mono g hg).2.le⟩,?_,?_⟩
  · have bound := forest_charge L pin
    have ledger := calcCost bs
    simp [init,List.map_map,Function.comp_def] at cost
    change F.gs.length+1≤C.size
    change (bs.map charge).sum≤C.size at bound
    omega
  · intro w len
    change (ResidualSurplus.run F.gs w).getD (F.ren C.output) false=(C.wires w).getD C.output false
    exact F.correct C.output seen ⟨w,len⟩

theorem no_shared_edge {C : Circuit} {n : Nat} (L : Layout C n) (pin : Id C → Nat)
    (internal : MeetsInternal L) (mini : T2SoleOrSplice.LexMinimum n C) (hn : 2≤n)
    (U W : Id C) (diff : U≠W) (p q : Nat) (a b : Tree)
    (ua : Block.group p a∈forest L pin) (wb : Block.group q b∈forest L pin)
    (outU : a.out=n+U.val) (outW : b.out=n+W.val)
    (lit : active L U W=true) : ∀ x∈a.raws,x∉b.raws := by
  classical
  intro x xa xb
  have ca : a.Checked C n := forest_checked L pin _ ua
  have cb : b.Checked C n := forest_checked L pin _ wb
  have ujoin : n+U.val∈a.gates := by
    cases a with
    | raw i => change i<n at ca; change i=n+U.val at outU; omega
    | external i => simp [Tree.raws] at xa
    | join j l r => change j=n+U.val at outU; simp [Tree.gates,outU]
  have neq : Block.group p a≠Block.group q b := by
    intro eq
    have h := congrArg Block.out eq
    change a.out=b.out at h
    rw [outU,outW] at h
    exact diff (Fin.ext (Nat.add_left_cancel h))
  have noU : n+U.val∉b.gates := by
    intro h
    have twice := distinct_parts _ _ _ neq ua wb _ ujoin h
    have mem : n+U.val∈allGates (forest L pin) := List.mem_flatMap.mpr ⟨_,ua,ujoin⟩
    have once := List.nodup_iff_count_eq_one.mp (forest_nodup L pin) _ mem
    omega
  have blit : on L U b.out=true := by simpa [outW,active] using lit
  obtain ⟨e,eb,ep⟩ := lit_external L U b cb noU blit
  obtain ⟨t,_,price,ts,ta⟩ := recipe x e b xb eb
  have flat (c : Tree) (tag : Nat) (check : c.Checked C n) (w : List Bool) (len : w.length=n) :
      (c.raws.any (fun i => w.getD i false) || c.exts.any (fun i => (C.wires w).getD i false))
      =(C.wires w).getD c.out false := by
    have h := ordinary_real (.group tag c) check w len (fun i => (C.wires w).getD i false)
      (fun _ _ => rfl)
    change (treeTerm c).value _ _=_ at h
    rw [flatten] at h
    exact h
  obtain ⟨D,mono,cost,same⟩ := save L pin internal (.group q b) t wb price
    (fun seen refs => ta n seen (rawBound b cb) refs) (by
      intro w len
      apply Eq.trans (ts _ _ ?_) (flat b q cb w len)
      intro rx
      have ax : a.raws.any (fun i => w.getD i false)=true := List.any_eq_true.mpr ⟨x,xa,rx⟩
      have hot := flat a p ca w len
      rw [ax,outU] at hot
      exact probe_le_actual L U (fun i => (C.wires w).getD i false)
        (fun i => (L.atIndex i).eval w len) (by simpa using hot.symm) e ep)
    (T2BenchmarkNormalize.output_internal mini.eligible)
  have computes : T2SoleOrSplice.Computes n D := by
    intro s
    rw [same _ (by simp [T2SoleOrSplice.vector])]
    exact mini.eligible.1 s
  obtain ⟨E,good,small⟩ := T2BenchmarkNormalize.canNormalize hn D mono computes
  have least := mini.primary E good
  omega

open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
theorem regular_no_shared_edge {n out : Nat} {gs : List Raw}
    (mini : LexMinimum n (source gs out)) (reg : Regular n gs) (hn : 2≤n)
    (pin : Id (source gs out) → Nat) (U W : Id (source gs out)) (diff : U≠W)
    (p q : Nat) (a b : Tree)
    (ua : Block.group p a∈forest (ThresholdRegularSource.layout n gs out mini.eligible) pin)
    (wb : Block.group q b∈forest (ThresholdRegularSource.layout n gs out mini.eligible) pin)
    (outU : a.out=n+U.val) (outW : b.out=n+W.val)
    (lit : active (ThresholdRegularSource.layout n gs out mini.eligible) U W=true) :
    ∀ x∈a.raws,x∉b.raws := by
  exact no_shared_edge _ pin (ThresholdRegularSource.regular_inputs n gs out mini.eligible reg).1
    mini hn U W diff p q a b ua wb outU outW lit

#print axioms regular_no_shared_edge
end ThresholdSharedPairMinimum
