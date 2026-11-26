import Batteries.Tactic.OpenPrivate
import T2LexMinimum
import T2SoleOrTopology
import Mathlib.Data.List.Induction

namespace T2BenchmarkNormalize
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice
open private run_app run_len run_old from T2SoleOrEval

def FitsWire (k : Nat) : Wire → Prop | .const _ => True | .live i => i<k

private theorem widen {a b : Nat} {w : Wire} (h : FitsWire a w) (le : a≤b) :
    FitsWire b w := by cases w <;> simp_all [FitsWire] <;> omega

/-- Lower additionally identifies equal live wires. Constant/variable combinations
    retain the already-proved GateSurplus.lower convention. -/
def binaryStep (o : Op) (l r : Wire) (k : Nat) : List Gate × Wire :=
  if l=r then ([],l) else lower o l r k

private theorem binaryStep_sem (o : Op) (l r : Wire) (v : List Bool) :
    let q := binaryStep o l r v.length
    read (run q.1 v) q.2=act o (read v l) (read v r) := by
  by_cases eq : l=r
  · subst r; cases o <;> simp [binaryStep,run,act]
  · simpa [binaryStep,eq] using lower_sound o l r v

private theorem binaryStep_shape (o : Op) (l r : Wire) (k : Nat)
    (hl : FitsWire k l) (hr : FitsWire k r) :
    let q := binaryStep o l r k
    SuffixOK k q.1 ∧ q.1.length≤1 ∧ FitsWire (k+q.1.length) q.2 := by
  by_cases same : l=r
  · simp [binaryStep,same,SuffixOK,hr]
  · simp only [binaryStep,if_neg same]
    cases l with
    | const a =>
      cases r with
      | const b => simp [lower,SuffixOK,FitsWire]
      | live i =>
        cases e : (a == neutral o) <;> simp_all [lower,SuffixOK,FitsWire]
    | live i =>
      cases r with
      | const b =>
        cases e : (b == neutral o) <;> simp_all [lower,SuffixOK,FitsWire]
      | live j =>
        exact ⟨⟨⟨o,i,j,rfl,hl,hr⟩,trivial⟩,by simp [lower],by simp [lower,FitsWire]⟩

def lowerInputs (o : Op) (xs : List Nat) (f : Nat → Wire) (k : Nat) : List Gate × Wire :=
  match xs with
  | [] => ([],.const (neutral o))
  | [x] => ([],f x)
  | x::y::_ => binaryStep o (f x) (f y) k

private theorem inputs_shape (o : Op) (xs : List Nat) (f : Nat → Wire) (k : Nat)
    (fit : ∀ i, FitsWire k (f i)) :
    let q := lowerInputs o xs f k
    SuffixOK k q.1 ∧ q.1.length≤1 ∧ FitsWire (k+q.1.length) q.2 := by
  cases xs with
  | nil => simp [lowerInputs,SuffixOK,FitsWire]
  | cons x tail =>
    cases tail with
    | nil => simpa [lowerInputs,SuffixOK] using fit x
    | cons y rest => exact binaryStep_shape o _ _ k (fit x) (fit y)

private theorem inputs_sem (o : Op) (xs : List Nat) (f : Nat → Wire) (v : List Bool)
    (small : xs.length≤2) :
    let q := lowerInputs o xs f v.length
    read (run q.1 v) q.2 = (gateOp o).eval (xs.map (fun i => read v (f i))) := by
  cases xs with
  | nil => cases o <;> rfl
  | cons x tail =>
    cases tail with
    | nil => cases o <;> simp [lowerInputs,run,gateOp,GateOp.eval]
    | cons y rest =>
      have er : rest=[] := by cases rest <;> simp_all
      subst rest
      have h := binaryStep_sem o (f x) (f y) v
      cases o <;> simpa [lowerInputs,gateOp,GateOp.eval,act] using h

structure Bank (n : Nat) (old : List Gate) where
  gs : List Gate
  ren : Nat → Wire
  shape : SuffixOK n gs
  cost : gs.length≤old.length
  fit : ∀ i, FitsWire (n+gs.length) (ren i)
  right : ∀ (v : List Bool), v.length=n → ∀ i,
    read (run gs v) (ren i)=(run old v).getD i false

private theorem start (n : Nat) : Nonempty (Bank n []) := by
  refine ⟨⟨[],fun i => if i<n then .live i else .const false,trivial,by simp,?_,?_⟩⟩
  · intro i; by_cases hi : i<n <;> simp [hi,FitsWire]
  · intro v len i
    by_cases hi : i<n
    · simp [hi,run,ResidualSurplus.read]
    · have bound : ¬i<v.length := by omega
      simp [hi,run,ResidualSurplus.read,List.getD_eq_getElem?_getD,bound]

private theorem get_push_ne (v : List Bool) (b : Bool) (i : Nat) (ne : i≠v.length) :
    (v++[b]).getD i false=v.getD i false := by
  by_cases hi : i<v.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
  · have gt : v.length < i := by omega
    have far : ¬ i<(v++[b]).length := by simp; omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt far),
      List.getElem?_eq_none (Nat.le_of_not_gt hi)]

private theorem oldWire (more : List Gate) (v : List Bool) (w : Wire)
    (fit : FitsWire v.length w) : read (run more v) w=read v w := by
  cases w with
  | const b => rfl
  | live i => exact run_old more v i fit

private theorem extend {n : Nat} {old : List Gate} (B : Bank n old) (g : Gate) (o : Op)
    (kind : g.op=gateOp o) (small : g.inputs.length≤2) : Nonempty (Bank n (old++[g])) := by
  let k := n+old.length
  let j := n+B.gs.length
  let q := lowerInputs o g.inputs B.ren j
  obtain ⟨ok,sz,bound⟩ := inputs_shape o g.inputs B.ren j B.fit
  refine ⟨⟨B.gs++q.1,fun i => if i=k then q.2 else B.ren i,
    (ok_append _ _ _).mpr ⟨B.shape,ok⟩,?_,?_,?_⟩⟩
  · change q.1.length≤1 at sz
    have hc := B.cost; simp only [List.length_append,List.length_singleton]; omega
  · intro i
    by_cases eq : i=k
    · simpa [eq,q,j,Nat.add_assoc] using bound
    · simpa [eq] using widen (w:=B.ren i) (B.fit i) (by simp : n+B.gs.length≤n+(B.gs++q.1).length)
  · intro v len i
    have jlen : (run B.gs v).length=j := by simp [run_len,len,j]
    have klen : (run old v).length=k := by simp [run_len,len,k]
    rw [run_app,run_app]
    change read (run q.1 (run B.gs v)) (if i=k then q.2 else B.ren i) =
      ((run old v)++[val g (run old v)]).getD i false
    by_cases eq : i=k
    · subst i; rw [if_pos rfl,←klen,getD_new]
      have h := inputs_sem o g.inputs B.ren (run B.gs v) small
      rw [jlen] at h
      simpa only [q,val,kind,B.right v len] using h
    · rw [if_neg eq,get_push_ne _ _ _ (by omega),oldWire _ _ _ (by rw [jlen]; exact B.fit i)]
      exact B.right v len i

private theorem build {n : Nat} (old : List Gate)
    (basis : ∀ g∈old, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    Nonempty (Bank n old) := by
  induction old using List.reverseRecOn with
  | nil => exact start n
  | append_singleton xs g ih =>
    obtain ⟨B⟩ := ih (fun a ha => basis a (by simp [ha]))
    obtain ⟨kind,small⟩ := basis g (by simp)
    rcases (show g.op=GateOp.and ∨ g.op=GateOp.or from by simpa using kind) with hand|hor
    · exact extend B g .and hand small
    · exact extend B g .or hor small

theorem canNormalize {n : Nat} (two : 2≤n) : CanNormalize n := by
  intro D mono correct
  obtain ⟨B⟩ := build (n:=n) D.gates mono
  have right (s : Finset (Fin n)) :
      read (run B.gs (vector s)) (B.ren D.output)=D.eval (vector s) :=
    B.right _ (by simp [vector]) _
  cases eq : B.ren D.output with
  | const b =>
    have zero := right ∅
    have full := right Finset.univ
    rw [eq] at zero full
    have pos : D.eval (vector (Finset.univ : Finset (Fin n)))=true :=
      (correct _).mpr (by simpa using two)
    have neg : D.eval (vector (∅ : Finset (Fin n)))≠true := by
      intro t; have := (correct _).mp t; simp at this
    change b=D.eval (vector (∅ : Finset (Fin n))) at zero
    change b=D.eval (vector (Finset.univ : Finset (Fin n))) at full
    exact False.elim (neg (zero.symm.trans (full.trans pos)))
  | live i =>
    let E : Circuit := ⟨B.gs,i⟩
    have bounded := B.fit D.output
    rw [eq] at bounded
    refine ⟨E,(eligible_iff n E).mpr ⟨?_,bounded,B.shape⟩,B.cost⟩
    intro s
    have sim := right s
    rw [eq] at sim
    change E.eval (vector s)=D.eval (vector s) at sim
    rw [sim]
    exact correct s

/-- A live eligible output can never be raw: use its own singleton as a
    rejecting witness, whereas the old raw bit on that row is true. -/
theorem output_internal {n : Nat} {C : Circuit} (h : Eligible n C) :
    ∃ j : Fin C.gates.length, C.output=n+j.val := by
  have large : n≤C.output := by
    by_contra! hi
    let i : Fin n := ⟨C.output,hi⟩
    let v := vector ({i} : Finset (Fin n))
    have len : v.length=n := by simp [v,vector]
    have raw : v.getD C.output false=true := by
      simp [v,vector,List.getD_eq_getElem?_getD,hi,i]
    have accepted : C.eval v=true := by
      change (run C.gates v).getD C.output false=true
      rw [run_old _ _ _ (by omega),raw]
    have impossible := (h.1 {i}).mp accepted
    simpa using impossible
  have fit := h.2.1
  refine ⟨⟨C.output-n,by omega⟩,?_⟩
  change C.output=n+(C.output-n)
  omega

#print axioms output_internal
#print axioms canNormalize
end T2BenchmarkNormalize
