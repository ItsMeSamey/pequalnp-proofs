import ThresholdLeakPins
import T2SoleOrSplice
namespace ThresholdOccurrenceEval
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrExtraction T2OrPartition ThresholdLeakPins
variable {C : Circuit} {n k : Nat} (L : Layout C n)
abbrev Assignment (C : Circuit) (k : Nat) := Pin C → Bool ⊕ Fin k
def value (a : Bool ⊕ Fin k) (s : Finset (Fin k)) : Bool :=
  match a with | .inl b => b | .inr j => decide (j∈s)
def fixedArg (a : Bool ⊕ Fin k) : Bool := match a with | .inl _ => true | .inr _ => false

def eval (A : Assignment C k) (s : Finset (Fin k)) (i : Id C) : Bool :=
  let atPin := fun b : Bool =>
    let q := (i,b)
    let w := source L q
    if h : w<n then value (A q) s
    else if ht : w-n < i.val then eval A s ⟨w-n,by have hh := i.isLt; omega⟩ else false
  act (L.op i) (atPin false) (atPin true)
termination_by i.val

def wire (A : Assignment C k) (s : Finset (Fin k)) (w : Nat) :=
  if ht : w-n<C.gates.length then eval L A s ⟨w-n,ht⟩ else false
def pinEval (A : Assignment C k) (s : Finset (Fin k)) (q : Pin C) : Bool :=
  if source L q<n then value (A q) s else wire L A s (source L q)

theorem earlier (q : Pin C) : source L q<n+q.1.val := by
  cases q with
  | mk i b => cases b
              · exact (L.atIndex i).leftEarlier
              · exact (L.atIndex i).rightEarlier

theorem row (A : Assignment C k) (s : Finset (Fin k)) (i : Id C) :
    eval L A s i=act (L.op i) (pinEval L A s (i,false)) (pinEval L A s (i,true)) := by
  rw [eval]
  have same (b : Bool) :
      (if h : source L (i,b)<n then value (A (i,b)) s else
        if h : source L (i,b)-n < i.val then eval L A s ⟨source L (i,b)-n,by have := i.isLt;omega⟩ else false)
        =pinEval L A s (i,b) := by
    have lt := earlier L (i,b)
    have fit := i.isLt
    by_cases h : source L (i,b)<n
    · simp [h,pinEval]
    · have a : source L (i,b)-n < i.val := by change source L (i,b)<n+i.val at lt; omega
      have z : source L (i,b)-n<C.gates.length := by omega
      simp [h,a,z,pinEval,wire]
  exact congrArg₂ (act (L.op i)) (same false) (same true)

@[simp] theorem wire_gate (A : Assignment C k) (s : Finset (Fin k)) (i : Id C) :
    wire L A s (n+i.val)=eval L A s i := by simp [wire,i.isLt]

def Const (f : Finset (Fin k) → Bool) : Prop := ∃ b,∀ s,f s=b
noncomputable def outFixed (A : Assignment C k) (i : Id C) : Bool := by
  classical exact decide (Const (fun s => eval L A s i))
noncomputable def pinFixed (A : Assignment C k) (q : Pin C) : Bool := by
  classical exact decide (Const (fun s => pinEval L A s q))

theorem fixed_link (A : Assignment C k) (q : Pin C) (a : Id C) (eq : source L q=n+a.val) :
    pinFixed L A q=outFixed L A a := by
  have same (s) : pinEval L A s q=eval L A s a := by rw [pinEval,eq]; simp
  unfold pinFixed outFixed
  rw [funext same]

theorem raw_fixed (A : Assignment C k) (q : Pin C) (e : source L q<n) :
    pinFixed L A q=fixedArg (A q) := by
  classical
  cases h : A q with
  | inl b => simp [pinFixed,pinEval,e,h,Const,value,fixedArg]
  | inr j =>
    have no : ¬Const (fun s : Finset (Fin k) => decide (j∈s)) := by
      rintro ⟨b,all⟩
      have off := all ∅
      have on := all {j}
      simp at off on; simp_all
    simpa [pinFixed,pinEval,e,h,value,fixedArg] using no

theorem fixed_both (A : Assignment C k) (i : Id C)
    (a : pinFixed L A (i,false)=true) (b : pinFixed L A (i,true)=true) :
    outFixed L A i=true := by
  classical
  obtain ⟨x,hx⟩ := of_decide_eq_true a
  obtain ⟨y,hy⟩ := of_decide_eq_true b
  apply decide_eq_true
  exact ⟨act (L.op i) x y,fun s => (row L A s i).trans (congrArg₂ (act (L.op i)) (hx s) (hy s))⟩
end ThresholdOccurrenceEval
