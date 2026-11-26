import ThresholdNamedIncidence
import ThresholdUniqueRaw
import T2CubeAgreement
import Mathlib.Combinatorics.SimpleGraph.Basic
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open T2SoleOrSplice ThresholdNamedIncidence
namespace ThresholdSimpleIncidence

noncomputable def labels {C : Circuit} {n : Nat} (L : Layout C n) (v : T2OrPartition.Id C) :=
  if (T2OrPartition.next C n v).isNone then rawList (makeBlock L Fin.val v) else []

noncomputable def endpoints {C : Circuit} {n : Nat} (L : Layout C n) (w : Fin n) :=
  Finset.univ.filter (fun v : T2OrPartition.Id C => w.val∈labels L v)

noncomputable def vertices {C : Circuit} {n : Nat} (L : Layout C n) :=
  Finset.univ.filter (fun v : T2OrPartition.Id C => labels L v≠[])

theorem active_endpoint {C : Circuit} {n : Nat} (L : Layout C n) (w : Fin n) :
    endpoints L w ⊆ vertices L := by
  intro v hv
  have h : w.val∈labels L v := by simpa [endpoints] using hv
  simp [vertices,List.ne_nil_of_mem h]

theorem endpoint_card {C : Circuit} {n : Nat} (L : Layout C n) (reg : MeetsInternal L)
    (hn : 2≤n) (mini : LexMinimum n C) (w : Fin n)
    (two : (T2OrPartition.readers C w.val).length=2) : (endpoints L w).card=2 := by
  let all := List.finRange C.gates.length
  let selected := all.filter (fun v => decide (w.val∈labels L v))
  have same : selected.toFinset=endpoints L w := by ext v; simp [selected,all,endpoints]
  have occurrence (v : T2OrPartition.Id C) (fixedV : (T2OrPartition.next C n v).isNone=true) :
      (rawList (makeBlock L Fin.val v)).count w.val =
        if w.val∈rawList (makeBlock L Fin.val v) then 1 else 0 := by
    have mem : makeBlock L Fin.val v ∈ forest L Fin.val := by
      exact List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨List.mem_finRange _,fixedV⟩,rfl⟩
    cases eq : makeBlock L Fin.val v with
    | meet j l r => simp [rawList]
    | group p t =>
      have nd := ThresholdUniqueRaw.group_raw_nodup L Fin.val reg hn mini (eq ▸ mem)
      exact nd.count
  have total (xs : List (T2OrPartition.Id C)) :
      (xs.filter (fun v => decide (w.val∈labels L v))).length =
      (((xs.filter (fun v => (T2OrPartition.next C n v).isNone)).map (makeBlock L Fin.val)).map
        (fun b => (rawList b).count w.val)).sum := by
    induction xs with
    | nil => rfl
    | cons v xs ih =>
      simp [labels] at ih
      cases e : T2OrPartition.next C n v with
      | none =>
        have count := occurrence v (by simp [e])
        by_cases mem : w.val∈rawList (makeBlock L Fin.val v) <;>
          simp [labels,List.filter_cons,e,mem,count,ih,Nat.add_comm]
      | some d => simp [labels,List.filter_cons,e,ih]
  calc
    _ = selected.toFinset.card := by rw [same]
    _ = selected.length := List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)
    _ = _ := total all
    _ = _ := (point_count L reg w.isLt Fin.val).trans two

theorem endpoint_profile {C : Circuit} {n : Nat} (L : Layout C n) (s : Finset (Fin n))
    (v : T2OrPartition.Id C) :
    (labels L v).any (fun z => (vector s).getD z false)=true ↔
      ∃ w∈s,v∈endpoints L w := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j,mem,on⟩
    rw [vec_get] at on
    split at on
    next small =>
      exact ⟨⟨j,small⟩,of_decide_eq_true on,by simpa [endpoints] using mem⟩
    next => contradiction
  · rintro ⟨w,hs,hit⟩
    refine ⟨w.val,by simpa [endpoints] using hit,?_⟩
    rw [vec_get]; simp [w.isLt,hs]

theorem endpoints_injective {C : Circuit} {n : Nat} (L : Layout C n) (D : Circuit)
    (rep : ∀ s : Finset (Fin n), D.eval (incidence (endpointLists L) (vector s))=true ↔ 2≤s.card) :
    Function.Injective (endpoints L) := by
  intro x y same
  by_contra ne
  have acts (v : T2OrPartition.Id C) :
      (labels L v).any (fun j => (vector ({x} : Finset (Fin n))).getD j false) =
      (labels L v).any (fun j => (vector ({x,y} : Finset (Fin n))).getD j false) := by
    apply Bool.eq_iff_iff.mpr
    change _ = true ↔ _ = true
    rw [endpoint_profile,endpoint_profile]
    simp [same]
  have profile : incidence (endpointLists L) (vector ({x} : Finset (Fin n))) =
      incidence (endpointLists L) (vector ({x,y} : Finset (Fin n))) := by
    simpa [incidence,endpointLists,labels,List.map_ofFn,Function.comp_def] using
      congrArg List.ofFn (funext acts)
  have yes := (rep {x,y}).mpr (by simp [ne])
  have no := (rep {x}).mp ((congrArg D.eval profile).trans yes)
  simp at no

noncomputable def graph {C : Circuit} {n : Nat} (L : Layout C n) :
    SimpleGraph {i : T2OrPartition.Id C // i∈vertices L} where
  Adj a b := a≠b ∧ ∃ w : Fin n,a.val∈endpoints L w ∧ b.val∈endpoints L w
  symm := by
    constructor
    rintro a b ⟨ne,w,ha,hb⟩
    exact ⟨Ne.symm ne,w,hb,ha⟩
  loopless := ⟨fun a h => h.1 rfl⟩

theorem classified_simple {n out : Nat} {gs : List ResidualSurplus.Raw}
    (hn : 2≤n) (mini : LexMinimum n (T2CubeDeletion.source gs out)) (reg : T2RegularOrDelete.Regular n gs) :
    let L := ThresholdRegularSource.layout n gs out mini.eligible
    (∀ w, (endpoints L w).card=2) ∧ Function.Injective (endpoints L) ∧
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ s : Finset (Fin n), D.eval (incidence (endpointLists L) (vector s))=true ↔ 2≤s.card) ∧
      ors D.gates+2*n≤ors (T2CubeDeletion.source gs out).gates+(batchVertices (forest L Fin.val)).length := by
  let L := ThresholdRegularSource.layout n gs out mini.eligible
  obtain ⟨regL,twice,_⟩ := regular_inputs n gs out mini.eligible reg
  obtain ⟨D,mono,rep,cost⟩ := classified_endpoints mini.eligible reg
  exact ⟨fun w => endpoint_card L regL hn mini w (twice w.val w.isLt),
    endpoints_injective L D rep,D,mono,rep,cost⟩


theorem vertices_card {C : Circuit} {n : Nat} (L : Layout C n) :
    (vertices L).card=(batchVertices (forest L Fin.val)).length := by
  let all := List.finRange C.gates.length
  let active := all.filter (fun v => decide (labels L v≠[]))
  have same : active.toFinset=vertices L := by ext v; simp [active,all,vertices]
  have works (b : Block) : (b.batch==1) = decide (rawList b≠[]) := by
    cases b with
    | meet => rfl
    | group p t => cases e : t.raws <;> simp [Block.batch,rawList,e]
  have hist (xs : List (T2OrPartition.Id C)) :
      (xs.filter (fun v => decide (labels L v≠[]))).length =
      (batchVertices ((xs.filter (fun v => (T2OrPartition.next C n v).isNone)).map (makeBlock L Fin.val))).length := by
    induction xs with
    | nil => rfl
    | cons v xs ih =>
      cases e : T2OrPartition.next C n v <;>
        by_cases mem : rawList (makeBlock L Fin.val v)=[] <;>
        simp [labels,batchVertices,e,works,mem] at ih ⊢ <;> omega
  calc
    _ = active.toFinset.card := by rw [same]
    _ = active.length := List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)
    _ = _ := hist all

#print axioms classified_simple
end ThresholdSimpleIncidence
