import DDPhysicalRows
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double
attribute [local instance] gateOpDecEq
/-- Original IDs travel with the refs even across bypassed ANDs. -/
inductive Origin | input (i : ℕ) | gate (i : ℕ) deriving DecidableEq
structure State where
  gates : List Gate
  refs : List (Option (Origin × ℕ))
def initial (n : ℕ) : State := ⟨[], (List.range n).map fun i => some (.input i,i)⟩
def ref (s : State) (w : ℕ) := s.refs.getD w none
def producer (s : State) (w : ℕ) : Option ℕ :=
  match ref s w with | some (.gate i,_) => some i | _ => none
def pin (s : State) (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) (b : Fin 2) :=
  let w := opnd C j b
  if n ≤ w ∧ p.bypass j b = true then none else ref s w
abbrev Ref := Option (Origin × ℕ)
def instruction (op : GateOp) (skip : Bool) : Ref → Ref → Option Gate
  | some a, some b => if skip then none else some ⟨op,[a.2,b.2]⟩
  | _, _ => none
def dest (op : GateOp) (skip : Bool) (j w : ℕ) (a b : Ref) : Ref :=
  if skip then none else
  match a,b with
  | some _, some _ => some (.gate j,w)
  | _,_ => if op = .and then a.orElse (fun _ => b) else none
def step (s : State) (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) : State :=
  let a := pin s n C p j 0
  let b := pin s n C p j 1
  let op := (gateAt C j).op
  ⟨s.gates ++ (instruction op (p.omit j) a b).toList,
    s.refs ++ [dest op (p.omit j) j (n+s.gates.length) a b]⟩
def build (n : ℕ) (C : Circuit) (p : Cuts) : ℕ → State
  | 0 => initial n
  | j+1 => step (build n C p j) n C p j
abbrev rank (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) := (build n C p j).gates.length
def ins (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) :=
  instruction (gateAt C j).op (p.omit j) (pin (build n C p j) n C p j 0)
    (pin (build n C p j) n C p j 1)
theorem gates_step (n : ℕ) (C : Circuit) (p : Cuts) (j : ℕ) :
    (build n C p (j+1)).gates = (build n C p j).gates ++ (ins n C p j).toList := rfl
theorem refs_length (n : ℕ) (C : Circuit) (p : Cuts) (k : ℕ) :
    (build n C p k).refs.length = n+k := by
  induction k with
  | zero => simp [build,initial]
  | succ k ih => simp [build,step,ih,Nat.add_assoc]
theorem stable_ref {n j w : ℕ} (C : Circuit) (p : Cuts) (hw : w < n+j) :
    ref (build n C p (j+1)) w = ref (build n C p j) w := by
  unfold ref
  change (_ ++ [_]).getD w none = _
  rw [List.getD_append _ _ _ _ (by rw [refs_length]; exact hw)]
theorem rank_mono {n : ℕ} (C : Circuit) (p : Cuts) {j k : ℕ} (h : j ≤ k) :
    rank n C p j ≤ rank n C p k := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    change _ ≤ (build n C p (k+1)).gates.length
    rw [gates_step,List.length_append]
    exact Nat.le_trans ih (Nat.le_add_right ..)
theorem paid_strict {n i j : ℕ} (C : Circuit) (p : Cuts) {g : Gate}
    (hi : ins n C p i = some g) (hij : i < j) :
    rank n C p i < rank n C p j := by
  have h := rank_mono (n:=n) C p hij
  have e : rank n C p (i+1) = rank n C p i + 1 := by
    change (build n C p (i+1)).gates.length = _
    simp [gates_step,hi]
  change rank n C p (i+1) ≤ rank n C p j at h
  rw [e] at h
  exact h
theorem retains_instruction {n j k : ℕ} (C : Circuit) (p : Cuts) {g : Gate}
    (hi : ins n C p j = some g) (hk : j < k) :
    (build n C p k).gates[rank n C p j]? = some g := by
  induction k, hk using Nat.le_induction with
  | base => simp [gates_step,hi,rank]
  | succ k hk ih =>
    rw [gates_step, List.getElem?_append_left (paid_strict C p hi hk)]
    exact ih
theorem row_ref {n j k : ℕ} (C : Circuit) (p : Cuts) (hk : j < k) :
    ref (build n C p k) (n+j) =
    dest (gateAt C j).op (p.omit j) j (n+rank n C p j)
      (pin (build n C p j) n C p j 0) (pin (build n C p j) n C p j 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    let s := build n C p j
    have hs : s.refs.length = n+j := refs_length n C p j
    let v := dest (gateAt C j).op (p.omit j) j (n+rank n C p j) (pin s n C p j 0) (pin s n C p j 1)
    change (s.refs ++ [v]).getD (n+j) none = v
    exact (congrArg (fun i => (s.refs ++ [v]).getD i none) hs.symm).trans (by simp [List.getD_eq_getElem?_getD])
  | succ k hk ih => rw [stable_ref C p (by omega),ih]
theorem paid_ref {n j k : ℕ} (C : Circuit) (p : Cuts) {g : Gate}
    (hi : ins n C p j = some g) (hk : j < k) :
    ref (build n C p k) (n+j) = some (.gate j,n+rank n C p j) := by
  rw [row_ref C p hk]
  unfold ins at hi
  cases h0 : pin (build n C p j) n C p j 0 <;> cases h1 : pin (build n C p j) n C p j 1 <;>
    cases ho : p.omit j <;> simp_all [instruction,dest]
theorem ordered_reader {n j k : ℕ} (C : Circuit) (p : Cuts) {a b : Origin × ℕ}
    (hk : j < k) (keep : p.omit j = false)
    (left : pin (build n C p j) n C p j 0 = some a)
    (right : pin (build n C p j) n C p j 1 = some b) :
    (build n C p k).gates[rank n C p j]? = some ⟨(gateAt C j).op,[a.2,b.2]⟩ := by
  exact retains_instruction C p (by simp [ins,left,right,keep,instruction]) hk
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
