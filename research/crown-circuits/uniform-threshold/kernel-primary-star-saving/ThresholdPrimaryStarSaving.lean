import ThresholdNativeStarSaving
import Batteries.Tactic.OpenPrivate

namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds
/-- Size minimality without a secondary gate-count requirement. -/
structure PrimarySizeMinimum (n : Nat) (C : Circuit) : Prop where
  eligible : Eligible n C
  primary : ∀ D, Eligible n D → C.size ≤ D.size
end T2SoleOrSplice


namespace ThresholdUniqueRaw

open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction

theorem group_raw_nodup_primary {C : Circuit} {n : Nat} (L : Layout C n) (pin : T2OrPartition.Id C → Nat)
    (internal : MeetsInternal L) (hn : 2≤n) (mini : T2SoleOrSplice.PrimarySizeMinimum n C)
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

end ThresholdUniqueRaw

namespace ThresholdStarRawSlots

open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition ThresholdOrExtraction
open ThresholdOrGroups ThresholdSimpleIncidence ThresholdRegularSource ThresholdLeakPins
open ThresholdNamedIncidence T2SoleOrSplice
variable {C : Circuit} {n : Nat} (L : Layout C n)

open private center_count from ThresholdStarRawSlots

theorem center_once_primary (U : Id C) (reg : MeetsInternal L) (hn : 2≤n) (M : PrimarySizeMinimum n C)
    (stop : next C n U=none) (x : Fin n) :
    (centerFiber L U x).card = if x∈star L U then 1 else 0 := by
  classical
  rw [center_count L U x stop]
  have mem := mem_roots L Fin.val U stop
  cases h : makeBlock L Fin.val U with
  | meet => simp [star,endpoints,labels,stop,h,rawList]
  | group p t =>
    have nd := ThresholdUniqueRaw.group_raw_nodup_primary L Fin.val reg hn M (h ▸ mem)
    simpa [star,endpoints,labels,stop,h,rawList] using (show t.raws.count x.val = _ from nd.count)

theorem fixed_card_primary {k : Nat} (U : Id C) (chosen : Fin n) (e : ↥(star L U) ≃ Fin k)
    (reg : MeetsInternal L) (hn : 2≤n) (M : PrimarySizeMinimum n C) (stop : next C n U=none)
    (two : ∀ x : Fin n, (readers C x.val).length=2) :
    (fixedPins L U chosen e).card = 2*n-k := by
  classical
  let F := fixedPins L U chosen e
  let name := fun p : Pin C => if h : source L p<n then (⟨source L p,h⟩ : Fin n) else chosen
  have pieces (x : Fin n) : F.filter (fun p => name p=x) =
      if x∈star L U then centerFiber L U x else fiber L x := by
    ext p
    by_cases h : source L p<n
    · let y : Fin n := ⟨source L p,h⟩
      by_cases yx : y=x
      · have nx : source L p=x.val := congrArg Fin.val yx
        by_cases st : x∈star L U <;> by_cases ce : center L U p <;>
          simp [F,fixedPins,choice,name,h,yx,nx,st,ce,centerFiber,fiber,y] at *
      · have nx : source L p≠x.val := fun z => yx (Fin.ext z)
        by_cases st : x∈star L U <;>
          simp [F,fixedPins,name,h,show (⟨source L p,h⟩ : Fin n)≠x from yx,st,centerFiber,fiber,nx]
    · have nx : source L p≠x.val := by intro z; rw [z] at h; exact h x.isLt
      by_cases st : x∈star L U <;> simp [F,fixedPins,name,h,st,centerFiber,fiber,nx]
  have counts (x : Fin n) : (F.filter (fun p => name p=x)).card +
      (if x∈star L U then 1 else 0) = 2 := by
    rw [pieces]
    by_cases st : x∈star L U
    · simp [st,center_once_primary L U reg hn M stop]
    · simp [st,all_fiber,two]
  have total := Finset.sum_congr (s₁:=Finset.univ) rfl (fun x _ => counts x)
  have fibers : (∑ x : Fin n, (F.filter (fun p => name p=x)).card) = F.card := by
    simpa using (Finset.sum_card_fiberwise_eq_card_filter F (Finset.univ : Finset (Fin n)) name)
  have kcard : (star L U).card=k := by simpa using Fintype.card_congr e
  rw [Finset.sum_add_distrib,fibers] at total
  have sumstar : (∑ x : Fin n, if x∈star L U then 1 else 0) = (star L U).card := by simp
  rw [sumstar,kcard] at total
  simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  have tot : F.card + k = n*2 := by simpa using total
  change F.card=2*n-k
  rw [Nat.mul_comm 2 n, ← tot, Nat.add_sub_cancel]

end ThresholdStarRawSlots

namespace ThresholdStarBypass

open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdRegularSource

theorem regular_forced_hot_primary {n out : Nat} {gs : List Raw}
    (M : PrimarySizeMinimum n (source gs out)) (reg : Regular n gs) (input : List Bool) (len : input.length=n)
    (u : Nat) (sel : Nat → Bool) (hot : ((source gs out).wires input).getD u false=true) :
    let C := source gs out
    let L := layout n gs out M.eligible
    run u sel false (fun j => input.getD j false) (forest L Fin.val)
      (fun _ => false) C.output = C.eval input := by
  intro C L
  obtain ⟨internal,twice,obs⟩ := regular_inputs n gs out M.eligible reg
  obtain ⟨book,_,_,_,seen⟩ := physical_book L internal Fin.val twice obs
  exact book_agrees input len u sel hot _ [] book (fun _ => false) (by simp) _ seen

end ThresholdStarBypass

namespace ThresholdStarBypass

open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdRegularSource ThresholdSimpleIncidence

theorem forced_nonempty_row_primary {n out : Nat} {gs : List Raw} (M : PrimarySizeMinimum n (source gs out))
    (reg : Regular n gs) (sel : Nat → Bool) (s : Finset (Fin n)) (x : Fin n)
    (u : T2OrPartition.Id (source gs out)) (xs : x∈s)
    (xu : u∈endpoints (layout n gs out M.eligible) x) :
    let L := layout n gs out M.eligible
    run (n+u.val) sel false (fun j => (vector s).getD j false)
      (forest L Fin.val) (fun _ => false) out=true ↔ 2≤s.card := by
  intro L
  rw [show run (n+u.val) sel false (fun j => (vector s).getD j false)
      (forest L Fin.val) (fun _ => false) out =
      (source gs out).eval (vector s) from regular_forced_hot_primary M reg _ (by simp [vector]) _ sel
        (endpoint_hot L s x u xs xu)]
  exact M.eligible.1 s

end ThresholdStarBypass

namespace ThresholdSlotEvaluation

open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2OrPartition ThresholdStarRawSlots ThresholdStarBypass ThresholdSimpleIncidence
open T2SoleOrSplice T2RegularOrDelete T2CubeDeletion ThresholdRegularSource

theorem truth_primary {n out k : Nat} {gs : List Raw} (M : PrimarySizeMinimum n (source gs out))
    (reg : Regular n gs) (u : Id (source gs out)) (x : Fin n)
    (hx : x∈star (layout n gs out M.eligible) u)
    (e : ↥(star (layout n gs out M.eligible) u) ≃ Fin k) (s : Finset (Fin k))
    (V : Nat → Bool)
    (T : Trace (layout n gs out M.eligible)
      (fun i b => input (layout n gs out M.eligible) u x e (fun j => decide (j∈s)) (i,b)) V)
    (stop : next (source gs out) n u=none) : V out=true ↔ 2≤s.card := by
  classical
  let L := layout n gs out M.eligible
  obtain ⟨internal,twice,obs⟩ := regular_inputs n gs out M.eligible reg
  obtain ⟨book,_,_,_,mem⟩ := physical_book L internal Fin.val twice obs
  have rb := split_readback L u x hx e _ V T internal stop book out mem
  rw [arm_vector] at rb
  rw [←rb]
  by_cases hs : s.Nonempty
  · obtain ⟨j,hj⟩ := hs
    have hit : u∈endpoints L ((embed e) j) := (Finset.mem_filter.mp (e.symm j).property).2
    simpa using forced_nonempty_row_primary M reg (fun _ => false) (s.map (embed e)) ((embed e) j) u
      (Finset.mem_map.mpr ⟨_,hj,rfl⟩) hit
  · have nil : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have hit : u∈endpoints L x := (Finset.mem_filter.mp hx).2
    have one := forced_nonempty_row_primary M reg (fun _ => false) {x} x u (by simp) hit
    have mono := scan_monotone (n+u.val) (fun _ => false) false
      (fun j => (vector (∅ : Finset (Fin n))).getD j false)
      (fun j => (vector {x}).getD j false)
      (by intro j; change (vector (∅ : Finset (Fin n))).getD j false=true → _; rw [vec_get]; split <;> simp)
      (forest L Fin.val) (fun _ => false) (fun _ => false) (fun _ h => h)
    simp only [Finset.map_empty,Finset.card_empty]
    constructor
    · intro on
      have bad := one.mp (mono out on)
      simp at bad
    · omega

end ThresholdSlotEvaluation

namespace T2MinimalLive

open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RawIsolation

open private rename_bound from T2SoleOrTopology

private theorem forbids_short_primary (n x out : Nat) (pre post : List Gate) (g : Gate)
    (minC : PrimarySizeMinimum n ⟨pre++g::post,out⟩) (hx : x<n+pre.length)
    (same : Computes n (short n x pre post out)) : False := by
  let C : Circuit := ⟨pre++g::post,out⟩
  let D := short n x pre post out
  have orig := (eligible_iff n C).mp minC.eligible
  have bound : out<n+pre.length+1+post.length := by
    simpa [C,Circuit.size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using orig.2.1
  have cut := (ok_append pre (g::post) n).mp orig.2.2
  have suffix : SuffixOK (n+pre.length+1) post := cut.2.2
  have shape : SuffixOK n D.gates := by
    apply (ok_append _ _ _).mpr
    exact ⟨cut.1,by simpa using ok_rename post (n+pre.length) x (n+pre.length+1) hx (by omega) suffix⟩
  have output : D.output<n+D.size := by
    have h := rename_bound (h:=n+pre.length) (x:=x) (k:=n+pre.length+1+post.length)
      (j:=out) hx (by omega) bound
    change ren (n+pre.length) x out<n+(pre++post.map _).length
    simp only [List.length_append,List.length_map]; omega
  have good : Eligible n D := (eligible_iff _ _).mpr ⟨same,output,shape⟩
  have impossible := minC.primary D good
  simp [D,Circuit.size,short] at impossible <;> omega

theorem consumer_at_minimum_primary (n x out : Nat) (pre post : List Gate) (g : Gate)
    (minC : PrimarySizeMinimum n ⟨pre++g::post,out⟩)
    (hx : x<n+pre.length) (obs : out≠n+pre.length) :
    ∃ a∈post, n+pre.length∈a.inputs := by
  by_contra! dead
  have orig := (eligible_iff n _).mp minC.eligible
  have bound : out<n+pre.length+1+post.length := by
    simpa [Circuit.size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using orig.2.1
  have suffix : SuffixOK (n+pre.length+1) post :=
    ((ok_append pre (g::post) n).mp orig.2.2).2.2
  apply forbids_short_primary n x out pre post g minC hx
  intro s
  rw [dead_short n x out pre post g hx suffix bound obs dead _ (by simp [vector])]
  exact orig.1 s

end T2MinimalLive

namespace ThresholdFanoutBudget

open PEqualNP.CircuitLowerBounds
open T2OrPartition

open ThresholdOrExtraction ThresholdOrGroups T2SoleOrSplice

theorem live_slots_primary {C : Circuit} {n : Nat} (L : Layout C n) (M : PrimarySizeMinimum n C)
    (i : Id C) (nonout : C.output ≠ n+i.val) : 1 ≤ (readers C (n+i.val)).length := by
  have g := L.atIndex i
  obtain ⟨pre,post,hg,hp⟩ := g.layout
  have eqC : C = ⟨pre ++ ResidualSurplus.binary (L.op i) (L.left i) (L.right i) :: post,
    C.output⟩ := by cases C; simp_all
  have m := T2MinimalLive.consumer_at_minimum_primary n (L.left i) C.output pre post
    (ResidualSurplus.binary (L.op i) (L.left i) (L.right i)) (eqC ▸ M)
    (hp ▸ g.leftEarlier) (hp ▸ nonout)
  obtain ⟨reader,mem,slot⟩ := m
  have actual : reader ∈ C.gates := by rw [hg]; simp [mem]
  obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp actual
  have physical : n+i.val ∈ (C.gates.get ⟨j,hj⟩).inputs := by simpa [ej,hp] using slot
  have hit := read_mem physical
  exact List.length_pos_of_mem hit

end ThresholdFanoutBudget

namespace ThresholdOccurrenceCompiler

open ThresholdOrGroups PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus ThresholdOrExtraction T2OrPartition
open ThresholdLeakPins ThresholdOccurrenceEval ThresholdOccurrenceRecipe ThresholdFactorExpr ThresholdFactorNetwork
open ThresholdOccurrenceDebit T2SoleOrSplice
variable {C : Circuit} {n k : Nat} (L : Layout C n) (A : Assignment C k)

theorem compile_saving_primary (hk : 0<k) (out : Id C) (obs : C.output=n+out.val)
    (non : outFixed L A out=false) (mini : PrimarySizeMinimum n C)
    (H : Finset (Id C)) (shared : ∀ i∈H, outFixed L A i=true ∧ 2≤ThresholdSharedFlow.fan L i) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+rawFixed L (pinFixed L A)+H.card≤C.size ∧
      ∀ s : Finset (Fin k),D.eval (vector s)=eval L A s out := by
  obtain ⟨D,dm,cost,ok⟩ := compile L A hk out non
  have live (i : Id C) (hi : outFixed L A i=true) : 1≤ThresholdSharedFlow.fan L i := by
    rw [ThresholdSharedFlow.fan_readers]
    apply ThresholdFanoutBudget.live_slots_primary L mini
    intro eq
    have same : i=out := Fin.ext (by omega)
    simp [same,non] at hi
  have price := telescope L (pinFixed L A) (outFixed L A) H (fixed_link L A) (fixed_both L A) live shared
  exact ⟨D,dm,by rw [cost]; exact price,ok⟩

end ThresholdOccurrenceCompiler

namespace ThresholdNativeStarSaving

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus T2OrPartition
open T2SoleOrSplice T2RegularOrDelete T2CubeDeletion ThresholdOrExtraction ThresholdRegularSource
open ThresholdStarRawSlots ThresholdSharedPartition ThresholdSharedOrBudget ThresholdSharedFlow
open ThresholdOccurrenceEval ThresholdOccurrenceDebit

theorem star_saving_primary {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : PrimarySizeMinimum n (source gs out)) (reg : Regular n gs)
    (u : Id (source gs out)) (hu : u∈hubs (source gs out) n) :
    let L := layout n gs out M.eligible
    let k := (ThresholdHubDegrees.raws L u).card
    let t := (ThresholdHubDegrees.after L u).card
    2≤k → ∃ D : Circuit, Monotone2 D ∧ Computes k D ∧
      D.size+(2*n-k)+t+1≤(source gs out).size := by
  classical
  intro L k t hk
  let C := source gs out
  let e : ↥(star L u) ≃ Fin k := (star L u).equivFin
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(star L u).card by change 0<k;omega)
  let A := choice L u x e
  obtain ⟨internal,twice,j,obs⟩ := regular_inputs n gs out M.eligible reg
  have hubMem (a : Id C) (h : a∈hubs C n) : a∈sharedGates C n :=
    (List.mem_filter.mp (List.mem_toFinset.mp h)).1
  have stop := shared_stops (hubMem u hu)
  have truth_primary (s : Finset (Fin k)) : eval L A s j=true ↔ 2≤s.card := by
    have h := ThresholdSlotEvaluation.truth_primary M reg u x hx e s (wire L A s) (trace L u x e s) stop
    change C.output=n+j.val at obs
    change wire L A s C.output=true ↔ _ at h
    simpa only [obs,wire_gate] using h
  have notFixed : outFixed L A j=false := by
    apply decide_eq_false
    rintro ⟨b,h⟩
    have hi := (truth_primary Finset.univ).mpr (by simpa using hk)
    have lo : eval L A ∅ j≠true := fun yes => by simpa using (truth_primary ∅).mp yes
    change ∀ s, eval L A s j=b at h
    rw [h] at hi lo
    exact lo hi
  let H := insert u (ThresholdHubDegrees.after L u)
  have paid (a : Id C) (ha : a∈H) : outFixed L A a=true ∧ 2≤fan L a := by
    have data : a=u ∨ (a∈hubs C n ∧ u≠a ∧ active L u a=true) := by
      simpa [H,ThresholdHubDegrees.after] using ha
    have hub : a∈hubs C n := data.elim (fun eq => eq ▸ hu) (fun h => h.1)
    refine ⟨?_,?_⟩
    · apply decide_eq_true
      refine ⟨true,fun s => ?_⟩
      have tr := trace L u x e s
      have hot := ThresholdSlotEvaluation.center_hot L u x hx e _ _ tr internal stop
      rcases data with eq | h
      · subst a; simpa [wire_gate] using hot
      · simpa only [wire_gate] using ThresholdSlotEvaluation.probe_lower L tr u hot a h.2.2
    · rw [fan_readers]
      simpa [sharedGates] using hubMem a hub
  obtain ⟨D,dm,price,agree⟩ := ThresholdOccurrenceCompiler.compile_saving_primary L A (by omega) j obs notFixed M H paid
  have rawPrice : rawFixed L (pinFixed L A)=2*n-k := by
    rw [←fixed_card_primary L u x e internal hn M stop (fun y => twice y y.isLt)]
    unfold rawFixed fixedPins
    congr 1
    ext p
    by_cases h : ThresholdLeakPins.source L p<n
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,h,raw_fixed L A p h]
      change fixedArg (A p)=true ↔ (A p).isLeft=true
      cases A p <;> rfl
    · simp [h]
  have hH : H.card=t+1 := Finset.card_insert_of_notMem (by simp [ThresholdHubDegrees.after])
  rw [rawPrice,hH] at price
  refine ⟨D,dm,fun s => by rw [agree]; exact truth_primary s,by omega⟩

end ThresholdNativeStarSaving

#print axioms ThresholdNativeStarSaving.star_saving_primary
