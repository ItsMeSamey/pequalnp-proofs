import IncidenceHoistRealize
import IncidenceZeroRestriction
namespace IncidenceRunPinCompile
open CircuitRewire IncidenceZeroRestriction
open IncidenceHoistCompile IncidenceHoistRealize

inductive Ref
  | zero | one | wire (i : Nat)
  deriving DecidableEq

def read {Z : Type} (Y : Nat → Set Z) : Ref → Set Z
  | .zero => ∅
  | .one => Set.univ
  | .wire i => Y i

def below (n : Nat) (r : Ref) := ∀ i, r=.wire i → i<n
inductive Act
  | reuse (r : Ref)
  | emit (g : Gate)

def fold (op : Op) (a b : Ref) : Act :=
  match op,a,b with
  | .zero,_,_ => .reuse .zero
  | .copy,a,_ => .reuse a
  | .join,.zero,b => .reuse b
  | .join,a,.zero => .reuse a
  | .join,.one,_ | .join,_,.one => .reuse .one
  | .meet,.zero,_ | .meet,_,.zero => .reuse .zero
  | .meet,.one,b => .reuse b
  | .meet,a,.one => .reuse a
  | op,.wire x,.wire y => .emit ⟨op,x,y⟩

def evalAct {Z : Type} (Y : Nat → Set Z) : Act → Set Z
  | .reuse r => read Y r
  | .emit g => g.eval Y

theorem fold_eval {Z : Type} (Y : Nat → Set Z) (op : Op) (a b : Ref) :
    evalAct Y (fold op a b) = op.eval (read Y a) (read Y b) := by
  cases op <;> cases a <;> cases b <;> simp [fold,evalAct,read,Gate.eval,Op.eval]

structure Program where
  gates : List Gate
  refs : Nat → Ref

def step (m n j : Nat) (p : Program) : Act → Program
  | .reuse r => ⟨p.gates,put p.refs (m+j) r⟩
  | .emit g => ⟨p.gates++[g],put p.refs (m+j) (.wire (n+p.gates.length))⟩

def action (m j : Nat) (code : Nat → Gate) (z force : Nat → Bool) (p : Program) : Act :=
  if z (m+j) then .reuse .zero else if force j then .reuse .one else
    fold (code j).op (p.refs (code j).left) (p.refs (code j).right)

def compile (m n : Nat) (code : Nat → Gate) (init : Nat → Ref) (z force : Nat → Bool) : Nat → Program
  | 0 => ⟨[],init⟩
  | j+1 =>
    let p := compile m n code init z force j
    step m n j p (action m j code z force p)

def loss (code : Nat → Gate) (z force : Nat → Bool) (j : Nat) :=
  z (code j).left || z (code j).right || force j

def charges (code : Nat → Gate) (z force : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j+1 => charges code z force j + if loss code z force j then 1 else 0
theorem dark_refs (m n : Nat) (code : Nat → Gate) (init : Nat → Ref) (z force : Nat → Bool)
    (iz : ∀ i<m, z i=true → init i=.zero) (s : Nat) :
    ∀ i<m+s, z i=true → (compile m n code init z force s).refs i=.zero := by
  induction s with
  | zero => simpa [compile] using iz
  | succ j ih =>
    intro i hi hz
    by_cases eq : i=m+j
    · subst i
      simp [compile,action,hz,step,put]
    · have h := ih i (by omega) hz
      cases act : action m j code z force (compile m n code init z force j) <;>
        simpa [compile,act,step,put,eq] using h

private theorem no_emit_left (op : Op) (b : Ref) (g : Gate) : fold op .zero b ≠ .emit g := by
  cases op <;> cases b <;> simp [fold]

private theorem no_emit_right (op : Op) (a : Ref) (g : Gate) : fold op a .zero ≠ .emit g := by
  cases op <;> cases a <;> simp [fold]

theorem room (m n : Nat) (code : Nat → Gate) (init : Nat → Ref) (z force : Nat → Bool)
    (iz : ∀ i<m, z i=true → init i=.zero) (s : Nat)
    (ord : ∀ j<s, OrderedBinary (code j) (m+j)) :
    (compile m n code init z force s).gates.length + charges code z force s ≤ s := by
  induction s with
  | zero => simp [compile,charges]
  | succ j ih =>
    let p := compile m n code init z force j
    have prev := ih (fun k hk => ord k (by omega))
    change p.gates.length + _ ≤ j at prev
    have ⟨hl,hr,_⟩ := ord j (by omega)
    have refuse (g : Gate) (emit : action m j code z force p = .emit g) :
        loss code z force j = false := by
      unfold action at emit
      split at emit
      · contradiction
      split at emit
      · contradiction
      rename_i nf
      have left : z (code j).left = false := by
        cases v : z (code j).left
        · rfl
        · have dark : p.refs (code j).left=.zero := dark_refs m n code init z force iz j _ hl v
          rw [dark] at emit
          exact False.elim (no_emit_left _ _ _ emit)
      have right : z (code j).right = false := by
        cases v : z (code j).right
        · rfl
        · have dark : p.refs (code j).right=.zero := dark_refs m n code init z force iz j _ hr v
          rw [dark] at emit
          exact False.elim (no_emit_right _ _ _ emit)
      simp [loss,left,right,nf]
    change (step m n j p (action m j code z force p)).gates.length + _ ≤ _
    cases a : action m j code z force p with
    | reuse r => simp only [step,charges]; split <;> omega
    | emit g => simp [step,charges,refuse g a]; omega

def Valid (n : Nat) : Act → Prop
  | .reuse r => below n r
  | .emit g => OrderedBinary g n

private theorem fold_valid (n : Nat) (op : Op) (a b : Ref) (ha : below n a) (hb : below n b) :
    Valid n (fold op a b) := by
  cases op <;> cases a <;> cases b <;> simp_all [fold,Valid,below,OrderedBinary]

theorem typed (m n : Nat) (code : Nat → Gate) (init : Nat → Ref) (z force : Nat → Bool)
    (bound : ∀ i<m, below n (init i)) (s : Nat) (ord : ∀ j<s, OrderedBinary (code j) (m+j)) :
    let p := compile m n code init z force s
    (∀ i<m+s, below (n+p.gates.length) (p.refs i)) ∧
      ∀ j (hj : j<p.gates.length), OrderedBinary p.gates[j] (n+j) := by
  induction s with
  | zero => simpa [compile] using bound
  | succ j ih =>
    let p := compile m n code init z force j
    obtain ⟨rb,gb⟩ := ih (fun k hk => ord k (by omega))
    change ∀ i<m+j, below (n+p.gates.length) (p.refs i) at rb
    have ⟨hl,hr,_⟩ := ord j (by omega)
    have valid : Valid (n+p.gates.length) (action m j code z force p) := by
      unfold action
      split
      · simp [Valid,below]
      split
      · simp [Valid,below]
      exact fold_valid _ _ _ _ (rb _ hl) (rb _ hr)
    change (∀ i<m+(j+1), below (n+(step m n j p (action m j code z force p)).gates.length)
      ((step m n j p (action m j code z force p)).refs i)) ∧
      ∀ k (hk : k<(step m n j p (action m j code z force p)).gates.length),
        OrderedBinary (step m n j p (action m j code z force p)).gates[k] (n+k)
    cases act : action m j code z force p with
    | reuse r =>
      rw [act] at valid
      refine ⟨?_,gb⟩
      intro i hi
      by_cases eq : i=m+j
      · simpa [step,put,eq,Valid] using valid
      · simpa [step,put,eq] using rb i (by omega)
    | emit g =>
      rw [act] at valid
      refine ⟨?_,?_⟩
      · intro i hi idx he
        by_cases eq : i=m+j
        · simp [step,put,eq] at he
          simp [step]; omega
        · have h := rb i (by omega) idx (by simpa [step,put,eq] using he)
          simp [step]; omega
      · intro k hk
        change k < (p.gates++[g]).length at hk
        change OrderedBinary ((p.gates++[g])[k]'hk) (n+k)
        by_cases early : k<p.gates.length
        · rw [List.getElem_append_left early]
          exact gb k early
        · change k < (p.gates++[g]).length at hk
          simp only [List.length_append,List.length_singleton] at hk
          have eq : k=p.gates.length := by omega
          subst k
          simpa [Valid] using valid

private theorem prefix_model {Z} {n : Nat} {Y : Nat → Set Z} (gs : List Gate) (g : Gate)
    (h : Models n Y (gs++[g])) : Models n Y gs := by
  intro i hi
  have eq := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at eq

private theorem monotone_gate {Z} (op : Op) {a b c d : Set Z}
    (ac : a⊆c) (bd : b⊆d) : op.eval a b ⊆ op.eval c d := by
  cases op with
  | join => exact Set.union_subset_union ac bd
  | meet => exact Set.inter_subset_inter ac bd
  | copy => exact ac
  | zero => exact Set.Subset.rfl

/-- A literal residual model brackets both original evaluations on every free input. -/
theorem sandwich {Z : Type} (m n : Nat) (code : Nat → Gate) (init : Nat → Ref)
    (z force : Nat → Bool) (L U Y : Nat → Set Z) (s : Nat)
    (inp : ∀ i<m, L i ⊆ read Y (init i) ∧ read Y (init i) ⊆ U i)
    (ord : ∀ j<s, OrderedBinary (code j) (m+j))
    (lo : ∀ j<s,L (m+j)=(code j).eval L) (up : ∀ j<s,U (m+j)=(code j).eval U)
    (dark : ∀ i<m+s,z i=true → L i=∅) (hot : ∀ j<s,force j=true → U (m+j)=Set.univ)
    (model : Models n Y (compile m n code init z force s).gates) :
    ∀ i<m+s,L i ⊆ read Y ((compile m n code init z force s).refs i) ∧
      read Y ((compile m n code init z force s).refs i) ⊆ U i := by
  induction s with
  | zero => simpa [compile] using inp
  | succ j ih =>
    let p := compile m n code init z force j
    let act := action m j code z force p
    change Models n Y (step m n j p act).gates at model
    have oldModel : Models n Y p.gates := by
      cases eq : act with
      | reuse r => simpa [eq,step] using model
      | emit g => exact prefix_model _ _ (by simpa [eq,step] using model)
    have old := ih (fun j hj => ord j (by omega)) (fun j hj => lo j (by omega))
      (fun j hj => up j (by omega)) (fun i hi => dark i (by omega))
      (fun j hj => hot j (by omega)) oldModel
    have ⟨hl,hr,_⟩ := ord j (by omega)
    have mid : L (m+j) ⊆ evalAct Y act ∧ evalAct Y act ⊆ U (m+j) := by
      dsimp [act,action]
      split
      next hz => simp [dark _ (by omega) hz,evalAct,read]
      split
      next hf => simp [hot _ (by omega) hf,evalAct,read]
      rw [fold_eval,lo _ (by omega),up _ (by omega)]
      exact ⟨monotone_gate _ (old _ hl).1 (old _ hr).1,
             monotone_gate _ (old _ hl).2 (old _ hr).2⟩
    intro i hi
    change L i ⊆ read Y ((step m n j p act).refs i) ∧ read Y ((step m n j p act).refs i) ⊆ U i
    by_cases eq : i=m+j
    · subst i
      cases e : act with
      | reuse r => simpa [e,step,put,evalAct] using mid
      | emit g =>
        have full : Models n Y (p.gates++[g]) := by simpa [e,step] using model
        have last := full p.gates.length (by simp)
        have law : Y (n+p.gates.length) = g.eval Y := by simpa using last
        simpa [e,step,put,evalAct,read,law] using mid
    · have prev := old i (by omega)
      cases e : act <;> simpa [e,step,put,eq,p] using prev

/-- Direct topological evaluation of the emitted constant-free binary gates. -/
def wires {Z : Type} (n : Nat) (B : Nat → Set Z) (gs : List Gate) : Nat → Set Z :=
  IncidenceHoistFlow.value B (fun j => gs.getD j ⟨.zero,0,0⟩) (fun _ => none) n gs.length

theorem wires_inputs {Z : Type} (n : Nat) (B : Nat → Set Z) (gs : List Gate)
    (i : Nat) (hi : i<n) : wires n B gs i = B i := by
  simpa only [wires,Nat.zero_add,IncidenceHoistFlow.value] using
    IncidenceHoistFlow.stable B (fun j => gs.getD j ⟨.zero,0,0⟩) (fun _ => none) n 0 gs.length i (by omega)

theorem wires_model {Z : Type} (n : Nat) (B : Nat → Set Z) (gs : List Gate)
    (ordered : ∀ j (hj : j<gs.length), OrderedBinary gs[j] (n+j)) : Models n (wires n B gs) gs := by
  intro j hj
  let code := fun j => gs.getD j ⟨.zero,0,0⟩
  have atCode (k : Nat) (hk : k<gs.length) : code k=gs[k] := by
    simp [code,List.getD_eq_getElem?_getD,hk]
  have earlier (k : Nat) (hk : k<gs.length) :
      (code k).left < n+k ∧ (code k).right < n+k := by
    rw [atCode k hk]
    exact ⟨(ordered k hk).1,(ordered k hk).2.1⟩
  have law := IncidenceHoistFlow.law B code (fun _ => none) n gs.length j hj (earlier j hj)
  simpa [wires,code,List.getD_eq_getElem?_getD,hj] using law

#print axioms sandwich
#print axioms room
#print axioms wires_model
end IncidenceRunPinCompile
