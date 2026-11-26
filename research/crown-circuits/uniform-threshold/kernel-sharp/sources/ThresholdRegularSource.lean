import ThresholdOrPhysicalBook
import T2RegularShape
import T2BenchmarkNormalize
import T2CubeDeletion

namespace ThresholdRegularSource
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete

def encode (r : Raw) := binary r.1 r.2.1 r.2.2

private theorem encoded (gs : List Raw) (out : Nat) :
    (source gs out).gates=gs.map encode := by
  unfold source encode
  congr 1

def named (gs : List Raw) (out : Nat) (i : T2OrPartition.Id (source gs out)) : Raw :=
  gs[i.val]'(by have hi := i.isLt; simpa [encoded] using hi)

private theorem named_mem (gs : List Raw) (out : Nat) (i : T2OrPartition.Id (source gs out)) :
    named gs out i∈gs := List.getElem_mem _

private theorem gate_named (gs : List Raw) (out : Nat) (i : T2OrPartition.Id (source gs out)) :
    (source gs out).gates.get i=encode (named gs out i) := by
  simp [List.get_eq_getElem,encoded,named]

def layout (n : Nat) (gs : List Raw) (out : Nat) (h : Eligible n (source gs out)) :
    Layout (source gs out) n where
  op i := (named gs out i).1
  left i := (named gs out i).2.1
  right i := (named gs out i).2.2
  atIndex i := by
    let G := (source gs out).gates
    have hi : i.val<G.length := i.isLt
    have phys : G[i.val]=encode (named gs out i) := gate_named gs out i
    have earlier := (h.2.2 i).2.2
    refine ⟨⟨G.take i.val,G.drop (i.val+1),?_,?_⟩,?_,?_⟩
    · change G=G.take i.val ++ encode (named gs out i) :: G.drop (i.val+1)
      rw [←phys,List.getElem_cons_drop hi,List.take_append_drop]
    · simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
    · apply earlier
      change _∈G[i.val].inputs
      rw [phys]; simp [encode,binary]
    · apply earlier
      change _∈G[i.val].inputs
      rw [phys]; simp [encode,binary]

private theorem read_weight (C : Circuit) (w : Nat) :
    (T2OrPartition.readers C w).length =
      (C.gates.map (fun g => (g.inputs.filter (· == w)).length)).sum := by
  let idx := List.finRange C.gates.length
  let f := fun j : Fin C.gates.length => ((C.gates.get j).inputs.filter (· == w)).map (fun _ => j)
  have sum (xs : List (Fin C.gates.length)) : (xs.flatMap f).length =
      (xs.map (fun j => ((C.gates.get j).inputs.filter (· == w)).length)).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [List.flatMap_cons,ih,f]
  change (idx.flatMap f).length=_
  rw [sum]
  conv_rhs => rw [←List.map_get_finRange C.gates,List.map_map]
  rfl

private theorem rows_to_ports (w : Nat) (gs : List Raw)
    (distinct : ∀ r∈gs,r.2.1≠r.2.2) :
    (gs.map (fun r => ((encode r).inputs.filter (· == w)).length)).sum =
    (gs.filter (rawReads w)).length := by
  induction gs with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨o,l,r⟩ := r
    have neq : l≠r := distinct (o,l,r) (by simp)
    have tail := ih (fun a ha => distinct a (by simp [ha]))
    by_cases hl : l=w <;> by_cases hr : r=w <;>
      simp_all [encode,binary,rawReads,List.filter_cons] <;> omega

theorem regular_inputs (n : Nat) (gs : List Raw) (out : Nat) (h : Eligible n (source gs out))
    (reg : Regular n gs) :
    MeetsInternal (layout n gs out h) ∧
      (∀ w<n, (T2OrPartition.readers (source gs out) w).length=2) ∧
      ∃ i : T2OrPartition.Id (source gs out), (source gs out).output=n+i.val := by
  refine ⟨?_,?_,T2BenchmarkNormalize.output_internal h⟩
  · intro i op
    let r := named gs out i
    change r.1 = .and at op
    change n≤r.2.1 ∧ n≤r.2.2
    have clash (w : Fin n) (reads : rawReads w.val r=true) : False := by
      have isOr := (reg.1 w).2 r (named_mem gs out i) reads
      rw [op] at isOr
      contradiction
    constructor
    · by_contra! small
      exact clash ⟨_,small⟩ (by simp [rawReads])
    · by_contra! small
      exact clash ⟨_,small⟩ (by simp [rawReads])
  · intro w hw
    rw [read_weight,encoded,List.map_map]
    exact (rows_to_ports w gs reg.2).trans (reg.1 ⟨w,hw⟩).1

theorem classified_pool {α : Type} {n m out : Nat} {gs : List Raw} (h : Eligible n (source gs out))
    (reg : Regular n gs) (pin : T2OrPartition.Id (source gs out) → Nat)
    (raw formal : α → List Bool) (src : ∀ a,(raw a).length=n) (dst : ∀ a,(formal a).length=m)
    (pins : ∀ b∈forest (layout n gs out h) pin,b.RealPin (source gs out) raw formal m) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ a,D.eval (formal a)=(source gs out).eval (raw a)) ∧
      ors D.gates+2*n≤ors (source gs out).gates+
        (batchVertices (forest (layout n gs out h) pin)).length := by
  obtain ⟨meet,twice,obs⟩ := regular_inputs n gs out h reg
  exact regular_pool _ meet pin twice obs raw formal src dst pins

def rawList : Block → List Nat
  | .meet .. => []
  | .group _ t => t.raws

noncomputable def endpointLists {n : Nat} {C : Circuit} (L : Layout C n) :=
  List.ofFn (fun i : T2OrPartition.Id C =>
    if (T2OrPartition.next C n i).isNone then rawList (makeBlock L Fin.val i) else [])

theorem source_pins {α : Type} {n : Nat} {C : Circuit} (L : Layout C n)
    (raw : α → List Bool) (src : ∀ a,(raw a).length=n) :
    ∀ b∈forest L Fin.val,
      b.RealPin C raw (fun a => incidence (endpointLists L) (raw a)) (endpointLists L).length := by
  intro b member
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
  have stopped : (T2OrPartition.next C n i).isNone = true := (List.mem_filter.mp hi).2
  have stoppedEq : T2OrPartition.next C n i = none := by simpa using stopped
  have checked := makeBlock_checked L Fin.val i
  have lookup : (endpointLists L)[i.val]?=some (rawList (makeBlock L Fin.val i)) := by
    simp [endpointLists,i.isLt,stoppedEq]
  have idx (q : Nat) (t : Tree) (eq : makeBlock L Fin.val i=.group q t) : q=i.val := by
    unfold makeBlock at eq
    split at eq <;> simp_all
  cases e : makeBlock L Fin.val i with
  | meet j l r => trivial
  | group q t =>
    obtain rfl := idx q t e
    rw [e] at checked lookup
    exact pin_real_of_lookup raw src (endpointLists L) _ t checked lookup

theorem classified_endpoints {n out : Nat} {gs : List Raw} (h : Eligible n (source gs out))
    (reg : Regular n gs) :
    let L := layout n gs out h
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ s : Finset (Fin n), D.eval (incidence (endpointLists L) (vector s))=true ↔ 2≤s.card) ∧
      ors D.gates+2*n≤ors (source gs out).gates+(batchVertices (forest L Fin.val)).length := by
  let L := layout n gs out h
  have src (s : Finset (Fin n)) : (vector s).length=n := by simp [vector]
  obtain ⟨D,mono,sem,price⟩ := classified_pool h reg Fin.val vector
    (fun s => incidence (endpointLists L) (vector s)) src (fun _ => by simp [incidence])
    (source_pins L vector src)
  exact ⟨D,mono,fun s => (congrArg (fun v => v=true) (sem s)).to_iff.trans (h.1 s),price⟩

#print axioms classified_endpoints
end ThresholdRegularSource
