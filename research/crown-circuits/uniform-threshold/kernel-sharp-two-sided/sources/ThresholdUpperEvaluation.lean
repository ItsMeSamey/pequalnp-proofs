import ThresholdUpperBank
import Mathlib.Algebra.BigOperators.Fin
namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds

/-- Evaluating all gates from the *original* raw assignment. -/
def wires (input : List Bool) (gs : List Gate) := advance input gs
def valAt (input : List Bool) (gs : List Gate) := value (wires input gs)
def valid (input : List Bool) (gs : List Gate) (b : Bit) := fits (wires input gs).length b
def Extension (gs hs : List Gate) := ∃ suffix, hs=gs++suffix

private theorem ext_trans {a b c : List Gate} (h : Extension a b) (k : Extension b c) :
    Extension a c := by
  obtain ⟨s,rfl⟩ := h
  obtain ⟨t,rfl⟩ := k
  exact ⟨s++t,by simp⟩

private theorem persists (x : List Bool) {g h : List Gate} (e : Extension g h) (b : Bit)
    (f : valid x g b) : valid x h b ∧ valAt x h b = valAt x g b := by
  obtain ⟨s,rfl⟩ := e
  obtain ⟨more,hm⟩ := advance_extends (wires x g) s
  have eq : wires x (g++s)=wires x g++more := (advance_append x g s).trans hm
  unfold valid valAt
  rw [eq]
  refine ⟨?_,value_append _ _ _ f⟩
  cases b with
  | none => trivial
  | some i =>
    change i<(wires x g).length at f
    change i<(_++more).length
    simp; omega

def Correct (x : List Bool) (gs : List Gate) (c : Build Bit) (truth : Bool) :=
  let q := c.run gs
  Extension gs q.2 ∧ valid x q.2 q.1 ∧ valAt x q.2 q.1=truth

private theorem from_result {x : List Bool} {gs : List Gate} {c : Build Bit} {t : Bool} {k}
    (r : Result x.length gs (wires x gs) (c.run gs) t k) : Correct x gs c t := by
  obtain ⟨add,eq,_,_,fit,val⟩ := r.suffix
  refine ⟨⟨add,eq⟩,?_,?_⟩
  · simpa [valid,wires,advance_size] using fit
  · unfold valAt wires
    rw [eq,advance_append]
    exact val

private theorem or_correct (x : List Bool) (g : List Gate) (a b : Bit)
    (ha : valid x g a) (hb : valid x g b) :
    Correct x g (disj x.length a b) (valAt x g a || valAt x g b) :=
  from_result (one_or _ _ _ (advance_size x g) _ _ ha hb)

private theorem and_correct (x : List Bool) (g : List Gate) (a b : Bit)
    (ha : valid x g a) (hb : valid x g b) :
    Correct x g (conj x.length a b) (valAt x g a && valAt x g b) :=
  from_result (one_and _ _ _ (advance_size x g) _ _ ha hb)

private theorem pure_correct (x : List Bool) (gs : List Gate) (b : Bit) (h : valid x gs b) :
    Correct x gs (pure b) (valAt x gs b) := ⟨⟨[],by simp⟩,h,rfl⟩

/-- Snapshot the outcome of independent wire builders, allowing any earlier
    result to be read after later builders have extended the physical circuit. -/
private theorem sequence_correct {α : Type} (x : List Bool) (gs : List Gate)
    (items : List α) (build : α → Build Bit) (truth : α → Bool)
    (ok : ∀ j∈items, ∀ h, Extension gs h → Correct x h (build j) (truth j)) :
    let q := (items.mapM build).run gs
    Extension gs q.2 ∧ (∀ b∈q.1,valid x q.2 b) ∧ q.1.map (valAt x q.2)=items.map truth := by
  induction items generalizing gs with
  | nil => exact ⟨⟨[],by simp⟩,by simp,rfl⟩
  | cons a items ih =>
    let p := (build a).run gs
    let q := (items.mapM build).run p.2
    obtain ⟨eg,fg,vg⟩ := ok a (by simp) gs ⟨[],by simp⟩
    change Extension gs p.2 at eg
    obtain ⟨eh,fh,vh⟩ := ih p.2 (fun j hj h e => ok j (by simp [hj]) h (ext_trans eg e))
    change Extension p.2 q.2 at eh
    have old := persists x eh p.1 fg
    rw [List.mapM_cons]
    change Extension gs q.2 ∧ (∀ b∈p.1::q.1,_) ∧ (p.1::q.1).map _=_
    exact ⟨ext_trans eg eh,fun b hb => (List.mem_cons.mp hb).elim (fun e => e ▸ old.1) (fh b),
      by change valAt x q.2 p.1 :: q.1.map (valAt x q.2) = truth a :: items.map truth; exact congrArg₂ List.cons (old.2.trans vg) vh⟩

def counters (c : Nat) := (List.range 9).map (fun j => decide (j<c))
def Invariant (x : List Bool) (gs : List Gate) (bank : List Bit) (c : Nat) :=
  (∀ j, valid x gs (bank.getD j none)) ∧
  ∀ j, j<9 → valAt x gs (bank.getD j none)=decide (j<c)

private theorem cell (x : List Bool) (g : List Gate) (old : List Bit) (b : Bit) (c j : Nat)
    (inv : Invariant x g old c) (fit : valid x g b) (hj : j<9) :
    Correct x g (do
      let t ← if j=0 then pure b else conj x.length b (old.getD (j-1) none)
      disj x.length (old.getD j none) t) (decide (j<c+(valAt x g b).toNat)) := by
  by_cases e : j=0
  · subst j
    have r := or_correct x g (old.getD 0 none) b (inv.1 _) fit
    simp only [ite_true,if_pos,pure_bind]
    have eq : (valAt x g (old.getD 0 none) || valAt x g b) = decide (0<c+(valAt x g b).toNat) := by
      rw [inv.2 _ hj]; cases valAt x g b <;> simp <;> omega
    rw [←eq]; exact r
  · simp only [if_neg e]
    let q := (conj x.length b (old.getD (j-1) none)).run g
    obtain ⟨eg,fg,vg⟩ := and_correct x g b (old.getD (j-1) none) fit (inv.1 _)
    change Extension g q.2 at eg
    have oldj := persists x eg (old.getD j none) (inv.1 _)
    obtain ⟨eh,fh,vh⟩ := or_correct x q.2 (old.getD j none) q.1 oldj.1 fg
    refine ⟨ext_trans eg eh,fh,?_⟩
    let last := (disj x.length (old.getD j none) q.1).run q.2
    change valAt x last.2 last.1 = _
    change valAt x last.2 last.1 = _ at vh
    rw [vh,oldj.2,vg,inv.2 j hj,inv.2 (j-1) (by omega)]
    apply Bool.eq_iff_iff.mpr
    cases valAt x g b <;> simp [Bool.or_eq_true,Bool.and_eq_true,Bool.toNat] <;> omega

theorem prefix_eval (x : List Bool) (g : List Gate) (old : List Bit) (b : Bit) (c : Nat)
    (inv : Invariant x g old c) (fit : valid x g b) :
    let q := (prefixStep x.length old b).run g
    Extension g q.2 ∧ (∀ t∈q.1,valid x q.2 t) ∧
      q.1.map (valAt x q.2)=counters (c+(valAt x g b).toNat) := by
  apply sequence_correct
  intro j hj h ext
  have held (i) := persists x ext (old.getD i none) (inv.1 i)
  have kept := persists x ext b fit
  have invh : Invariant x h old c :=
    ⟨fun i => (held i).1,fun i hi => (held i).2.trans (inv.2 i hi)⟩
  simpa [kept.2] using cell x h old b c j invh kept.1 (List.mem_range.mp hj)
end ThresholdThreeLayerUpper

namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds
private theorem counters_inv (x : List Bool) (g : List Gate) (old : List Bit) (c : Nat)
    (fit : ∀ t∈old,valid x g t) (ev : old.map (valAt x g)=counters c) :
    Invariant x g old c := by
  constructor
  · intro j
    cases e : old[j]? with
    | none => simp [List.getD_eq_getElem?_getD,e,valid,fits]
    | some b =>
      have hb := List.mem_of_getElem? e
      simpa [List.getD_eq_getElem?_getD,e] using fit b hb
  · intro j hj
    have h := congrArg (fun l : List Bool => l[j]?) ev
    simp [counters,List.getElem?_map,List.getElem?_range,hj] at h
    cases e : old[j]? <;> simp_all [List.getD_eq_getElem?_getD]

theorem module_eval (x : List Bool) (g : List Gate) (old ports : List Bit) (c : Nat)
    (inv : Invariant x g old c) (fit : ∀ t∈ports,valid x g t) :
    let q := (ports.foldlM (prefixStep x.length) old).run g
    Extension g q.2 ∧ Invariant x q.2 q.1 (c+(ports.map (valAt x g)).count true) := by
  induction ports generalizing g old c with
  | nil => simpa using And.intro (show Extension g g from ⟨[],by simp⟩) inv
  | cons b bs ih =>
    let q := (prefixStep x.length old b).run g
    obtain ⟨eg,fg,vg⟩ := prefix_eval x g old b c inv (fit b (by simp))
    change Extension g q.2 at eg
    have ni := counters_inv x q.2 q.1 _ fg vg
    have keep (t) (ht : t∈bs) := persists x eg t (fit t (by simp [ht]))
    obtain ⟨et,it⟩ := ih q.2 q.1 _ ni (fun t ht => (keep t ht).1)
    have same : bs.map (valAt x q.2)=bs.map (valAt x g) := by
      apply List.map_congr_left
      intro t ht
      exact (keep t ht).2
    rw [same] at it
    refine ⟨ext_trans eg et,?_⟩
    let last := (bs.foldlM (prefixStep x.length) q.1).run q.2
    change Invariant x last.2 last.1 _
    change Invariant x last.2 last.1 _ at it
    cases e : valAt x g b <;> simpa [List.count_cons,e,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using it

theorem nine_eval (x : List Bool) (g : List Gate) (ports : List Bit)
    (fit : ∀ t∈ports,valid x g t) :
    let q := (ports.foldlM (prefixStep x.length) (List.replicate 9 none)).run g
    valAt x q.2 (q.1.getD 8 none)=decide (9≤(ports.map (valAt x g)).count true) := by
  have start : Invariant x g (List.replicate 9 none) 0 := by
    have nils (j : Nat) : (List.replicate 9 (none : Bit)).getD j none = none := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_replicate]
      split <;> rfl
    constructor
    · intro j; rw [nils]; trivial
    · intro j hj; rw [nils]; simp [valAt,value]
  have h := (module_eval x g (List.replicate 9 none) ports 0 start fit).2.2 8 (by decide)
  simpa only [Nat.zero_add,Nat.lt_iff_add_one_le] using h
end ThresholdThreeLayerUpper

namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds
def Marks {p} (x : List Bool) (g : List Gate) (src : List Bit) (S : Finset (Fin p)) :=
  (∀ i : Fin p,valid x g (src.getD i.val none)) ∧
  ∀ i : Fin p,valAt x g (src.getD i.val none)=decide (i∈S)

theorem layer_eval {p q} (x : List Bool) (g : List Gate) (adj : Fin p → Finset (Fin q))
    (src : List Bit) (S : Finset (Fin p)) (srcOk : Marks x g src S) :
    let r := (layer x.length adj src).run g
    Extension g r.2 ∧ (∀ t∈r.1,valid x r.2 t) ∧
    r.1.map (valAt x r.2)=List.ofFn (fun j => decide (j∈S.biUnion adj)) := by
  classical
  unfold layer
  rw [List.ofFn_eq_map]
  apply sequence_correct
  intro j hj h ext
  let bits := operands adj src j
  have held i := persists x ext (src.getD (i : Fin p).val none) (srcOk.1 i)
  have hfit (t) (ht : t∈bits) : valid x h t := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    exact (held i).1
  have nextBound := fiber_sem x.length h (wires x h) none bits (advance_size x h) (by trivial) hfit
  have truth : decide (j∈S.biUnion adj)=(false || bits.any (valAt x h)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.false_or,decide_eq_true_eq,List.any_eq_true,Finset.mem_biUnion]
    constructor
    · rintro ⟨i,si,ij⟩
      exact ⟨_,List.mem_map.mpr ⟨i,by simp [ij],rfl⟩,by rw [(held i).2,srcOk.2]; simp [si]⟩
    · rintro ⟨t,ht,hot⟩
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
      rw [(held i).2,srcOk.2] at hot
      exact ⟨i,of_decide_eq_true hot,by simpa using (List.mem_filter.mp hi).2⟩
  rw [truth]
  exact from_result nextBound

theorem marks_of_values {p} (x : List Bool) (g : List Gate) (src : List Bit) (S : Finset (Fin p))
    (fit : ∀ t∈src,valid x g t)
    (ev : src.map (valAt x g)=List.ofFn (fun i => decide (i∈S))) : Marks x g src S := by
  have len := congrArg List.length ev
  simp at len
  have idx (i : Fin p) : i.val<src.length := by omega
  constructor
  · intro i
    simpa [List.getD_eq_getElem?_getD,idx] using fit (src[i.val]'(idx i)) (List.getElem_mem _)
  · intro i
    have e := congrArg (fun a : List Bool => a[i.val]?) ev
    simpa [List.getD_eq_getElem?_getD,idx,i.isLt] using e

theorem actual_final_bits {n v w z} (L : Layers n v w z) (x : List Bool) (len : x.length=n)
    (S : Finset (Fin n)) (input : Marks x [] ((List.range n).map some) S) :
    valAt x ((program L).run []).2 ((program L).run []).1 =
      decide (9 ≤ (S.biUnion (support L)).card) := by
  classical
  let a := (layer x.length L.first ((List.range n).map some)).run []
  let b := (layer x.length L.second a.1).run a.2
  let c := (layer x.length L.third b.1).run b.2
  obtain ⟨_,fa,ea⟩ := layer_eval x [] L.first _ S input
  obtain ⟨_,fb,eb⟩ := layer_eval x a.2 L.second a.1 _ (marks_of_values x a.2 a.1 _ fa ea)
  obtain ⟨_,fc,ec⟩ := layer_eval x b.2 L.third b.1 _ (marks_of_values x b.2 b.1 _ fb eb)
  have h := nine_eval x c.2 c.1 fc
  let T := ((S.biUnion L.first).biUnion L.second).biUnion L.third
  change c.1.map (valAt x c.2) = List.ofFn (fun i => decide (i∈T)) at ec
  have assoc : T=S.biUnion (support L) := by ext j; simp [T,support,Finset.mem_biUnion]; aesop
  have countBits : (List.ofFn (fun i => decide (i∈T))).count true=T.card := by
    have aux (l : List Bool) : l.count true=(l.map Bool.toNat).sum := by
      induction l with
      | nil => rfl
      | cons b l ih => cases b <;> simp [List.count_cons,ih,Nat.add_comm]
    rw [aux,List.map_ofFn,List.sum_ofFn]
    simp [Bool.toNat]
  rw [ec,countBits,assoc] at h
  subst n
  exact h
end ThresholdThreeLayerUpper

namespace ThresholdThreeLayerUpper
open PEqualNP.CircuitLowerBounds
def activeInputs (n : Nat) (x : List Bool) := Finset.univ.filter (fun i : Fin n => x.getD i.val false)

theorem circuit_eval {n v w z} (L : Layers n v w z) (x : List Bool) (len : x.length=n) :
    (circuit L).eval x = decide (2≤(activeInputs n x).card) := by
  classical
  let S := activeInputs n x
  have input : Marks x [] ((List.range n).map some) S := by
    constructor
    · intro i
      simpa [valid,wires,advance,fits,List.getD_eq_getElem?_getD,i.isLt,len] using i.isLt
    · intro i
      simp [valAt,wires,advance,value,S,activeInputs,List.getD_eq_getElem?_getD,i.isLt]
  have h := actual_final_bits L x len S input
  rw [show decide (9≤(S.biUnion (support L)).card)=decide (2≤S.card) from
    by simp only [threshold L S]] at h
  let r := (program L).run []
  change valAt x r.2 r.1 = _ at h
  change (wires x r.2).getD (r.1.getD (n+r.2.length)) false = _
  cases e : r.1 with
  | some j => simpa [e,valAt,value] using h
  | none =>
    have endOf := advance_size x r.2
    change (wires x r.2).length=_ at endOf
    rw [len] at endOf
    simpa [e,valAt,value,List.getD_eq_getElem?_getD,←endOf] using h
end ThresholdThreeLayerUpper
