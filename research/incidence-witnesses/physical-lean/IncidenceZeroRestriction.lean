import Research.CircuitRewire

namespace IncidenceZeroRestriction
open CircuitRewire

/-- Literal zero propagation. Two available operands emit one row even when
their forwarded indices coincide. Thus the size equality holds before cleanup. -/
def literal (op : Op) (l r : Option Nat) : Action :=
  match op,l,r with
  | .zero,_,_ => .reuse none
  | .copy,x,_ => .reuse x
  | .join,none,x | .join,x,none => .reuse x
  | .meet,none,_ | .meet,_,none => .reuse none
  | op,some a,some b => .emit ⟨op,a,b⟩

theorem literal_eval {Z : Type*} (Y : ℕ → Set Z) (op : Op) (l r : Option ℕ) :
    (literal op l r).eval Y=op.eval (CircuitRewire.read Y l) (CircuitRewire.read Y r) := by
  cases op <;> cases l <;> cases r <;> simp [literal,Action.eval,CircuitRewire.read,Gate.eval,Op.eval]
theorem literal_reuse {op l r t} (h : literal op l r=.reuse t) :
    t=none ∨ t=l ∨ t=r := by
  cases op <;> cases l <;> cases r <;> simp_all [literal]
theorem literal_emit {op l r g} (h : literal op l r=.emit g) :
    l=some g.left ∧ r=some g.right ∧ (g.op=.join ∨ g.op=.meet) := by
  cases op <;> cases l <;> cases r <;> simp_all [literal]
  all_goals subst g; simp

def compileLiteral (m n : Nat) (raw : Nat→Gate) (initial : Nat→Option Nat) : Nat→Program
  | 0 => ⟨0,fun _=>⟨.zero,0,0⟩,initial⟩
  | j+1 =>
    let p := compileLiteral m n raw initial j
    let g := raw j
    advance p m n j (literal g.op (p.refs g.left) (p.refs g.right))

def OrderedBinary (g : Gate) (j : Nat) := g.left < j ∧ g.right < j ∧ (g.op=.join ∨ g.op=.meet)

def CorrectLiteral {Z : Type*} (m n j : Nat) (X B : Nat→Set Z) (init : Nat→Option Nat)
    (p : Program) : Prop :=
  (∀ i <m,p.refs i=init i) ∧ (∀ i <m+j,Below (n+p.size) (p.refs i)) ∧
  (∀ a <p.size,OrderedBinary (p.code a) (n+a)) ∧
  ∃ Y : Nat→Set Z,(∀ i <n,Y i=B i) ∧ (∀ a <p.size,Y (n+a)=(p.code a).eval Y) ∧
    ∀ i <m+j,X i=CircuitRewire.read Y (p.refs i)

private theorem oldRead {Z : Type*} (Y : ℕ → Set Z) (i : ℕ) (val : Set Z) (r : Option ℕ)
    (hr : Below i r) : CircuitRewire.read (put Y i val) r = CircuitRewire.read Y r := by
  cases r with
  | none => rfl
  | some j => exact ite_eq_right (Nat.ne_of_lt (hr j rfl))

private theorem oldGate {Z : Type*} (Y : ℕ → Set Z) (i : ℕ) (val : Set Z) (g : Gate)
    (ha : g.left < i) (hb : g.right < i) : g.eval (put Y i val) = g.eval Y := by
  simp [Gate.eval,put,Nat.ne_of_lt ha,Nat.ne_of_lt hb]

theorem literal_correct {Z : Type*} (m n s : ℕ) (raw : ℕ → Gate)
    (initial : ℕ → Option ℕ) (X B : ℕ → Set Z)
    (bound : ∀ j < m, Below n (initial j))
    (input : ∀ j < m, X j = CircuitRewire.read B (initial j))
    (ordered : ∀ g < s, (raw g).left < m+g ∧ (raw g).right < m+g)
    (sem : ∀ g < s, X (m+g) = (raw g).eval X) :
    CorrectLiteral m n s X B initial (compileLiteral m n raw initial s) := by
  induction s with
  | zero =>
    exact ⟨fun _ _ => rfl,bound,fun _ h => by simp [compileLiteral] at h,B,fun _ _ => rfl,fun _ h => by simp [compileLiteral] at h,input⟩
  | succ k ih =>
    let p := compileLiteral m n raw initial k
    obtain ⟨ini,prevBound,prevNorm,Y,hY,hG,hR⟩ := ih
      (fun g hg => ordered g (by omega)) (fun g hg => sem g (by omega))
    change (∀ j < m, p.refs j = initial j) at ini
    change (∀ j < m+k, Below (n+p.size) (p.refs j)) at prevBound
    change (∀ g < p.size, OrderedBinary (p.code g) (n+g)) at prevNorm
    change (∀ g < p.size, Y (n+g) = (p.code g).eval Y) at hG
    change (∀ j < m+k, X j = CircuitRewire.read Y (p.refs j)) at hR
    have ord := ordered k (by omega)
    let act := literal (raw k).op (p.refs (raw k).left) (p.refs (raw k).right)
    have eq : X (m+k) = act.eval Y := by
      rw [sem k (by omega)]
      unfold Gate.eval
      rw [hR _ ord.1,hR _ ord.2]
      exact (literal_eval _ _ _ _).symm
    change CorrectLiteral m n (k+1) X B initial (advance p m n k act)
    cases e : act with
    | reuse r =>
      simp only [advance]
      have rr := literal_reuse (show literal _ _ _ = .reuse r from e)
      have rb : Below (n+p.size) r := by
        rcases rr with rfl|rfl|rfl
        · intro j h; cases h
        · exact prevBound _ ord.1
        · exact prevBound _ ord.2
      refine ⟨?_,?_,prevNorm,Y,hY,hG,?_⟩
      · intro j hj; simp [put,show j ≠ m+k by omega,ini j hj]
      · intro j hj
        by_cases same : j=m+k
        · subst j; simpa [put] using rb
        · simpa [put,same] using prevBound j (by omega)
      · intro j hj
        by_cases same : j=m+k
        · subst j; simpa [put,e,Action.eval] using eq
        · simpa [put,same] using hR j (by omega)
    | emit g =>
      simp only [advance]
      obtain ⟨fl,fr,binary⟩ := literal_emit (show literal _ _ _ = .emit g from e)
      have left := prevBound _ ord.1 _ fl
      have right := prevBound _ ord.2 _ fr
      let val := g.eval Y
      let Y' := put Y (n+p.size) val
      refine ⟨?_,?_,?_,Y',?_,?_,?_⟩
      · intro j hj; simp [put,show j ≠ m+k by omega,ini j hj]
      · intro j hj v hv
        by_cases same : j=m+k
        · subst j; simp [put] at hv; change v < n + (p.size+1); omega
        · simp [put,same] at hv
          have := prevBound j (by omega) v hv
          dsimp; omega
      · intro h hh
        by_cases same : h=p.size
        · subst h; simpa [put,OrderedBinary] using (show OrderedBinary g (n+p.size) from ⟨left,right,binary⟩)
        · have lt : h < p.size := by dsimp at hh; omega
          simpa [put,same] using prevNorm h lt
      · intro j hj; simp [Y',put,show j ≠ n+p.size by omega,hY j hj]
      · intro h hh
        by_cases same : h=p.size
        · subst h; simpa [Y',put,val] using (oldGate Y (n+p.size) val g left right).symm
        · have lt : h < p.size := by dsimp at hh; omega
          have norms := prevNorm h lt
          have lg : (p.code h).left < n+p.size := lt_trans norms.1 (by omega)
          have rg : (p.code h).right < n+p.size := lt_trans norms.2.1 (by omega)
          change Y' (n+h) = (put p.code p.size g h).eval Y'
          rw [show put p.code p.size g h = p.code h from ite_eq_right same]
          rw [show (p.code h).eval Y' = _ from oldGate Y _ val _ lg rg]
          simpa [Y',put,same] using hG h lt
      · intro j hj
        by_cases same : j=m+k
        · subst j; simpa [put,CircuitRewire.read,Y',val,e,Action.eval] using eq
        · have lt : j<m+k := by omega
          change X j = CircuitRewire.read Y' (put p.refs (m+k) (some (n+p.size)) j)
          rw [show put p.refs (m+k) (some (n+p.size)) j = _ from ite_eq_right same]
          exact (hR j lt).trans (oldRead Y _ val _ (prevBound j lt)).symm


def deadOut (op : Op) (l r : Bool) : Bool :=
  match op with
  | .join => l && r
  | .meet => l || r
  | .copy => l
  | .zero => true

def lost (raw : Nat→Gate) (dead : Nat→Bool) (i : Nat) : Bool :=
  dead (raw i).left || dead (raw i).right

def charged (raw : Nat→Gate) (dead : Nat→Bool) (j : Nat) : Nat :=
  ((Finset.range j).filter fun i=>lost raw dead i=true).card

theorem charged_succ (raw : Nat→Gate) (dead : Nat→Bool) (j : Nat) :
    charged raw dead (j+1)=charged raw dead j+(if lost raw dead j then 1 else 0) := by
  unfold charged
  rw [Finset.range_add_one,Finset.filter_insert]
  cases h : lost raw dead j <;> simp [h,Finset.mem_filter]

private theorem literal_local (m n j : Nat) (p : Program) (g : Gate)
    (h : g.op=.join ∨ g.op=.meet) :
    let l := p.refs g.left
    let r := p.refs g.right
    let next := advance p m n j (literal g.op l r)
    (next.refs (m+j)).isNone=deadOut g.op l.isNone r.isNone ∧
    next.size+(if l.isNone || r.isNone then 1 else 0)=p.size+1 ∧
    ∀ a,a≠m+j → next.refs a=p.refs a := by
  rcases h with h|h <;> cases hl : p.refs g.left <;> cases hr : p.refs g.right <;>
    simp [h,hl,hr,literal,advance,deadOut,put] <;> aesop

theorem literal_counts (m n s : Nat) (raw : Nat→Gate) (init : Nat→Option Nat) (dead : Nat→Bool)
    (inputs : ∀ i < m,(init i).isNone=dead i)
    (order : ∀ j < s,OrderedBinary (raw j) (m+j))
    (dense : ∀ j < s,dead (m+j)=deadOut (raw j).op (dead (raw j).left) (dead (raw j).right)) :
    let p := compileLiteral m n raw init s
    (∀ i < m+s,(p.refs i).isNone=dead i) ∧ p.size+charged raw dead s=s := by
  induction s with
  | zero => simpa [compileLiteral,charged] using inputs
  | succ j ih =>
    let p := compileLiteral m n raw init j
    have o := order j (by omega)
    obtain ⟨agree,count⟩ := ih (fun i hi=>order i (by omega)) (fun i hi=>dense i (by omega))
    have l : (p.refs (raw j).left).isNone=dead (raw j).left := agree _ o.1
    have r : (p.refs (raw j).right).isNone=dead (raw j).right := agree _ o.2.1
    obtain ⟨new,size,old⟩ := literal_local m n j p (raw j) o.2.2
    change p.size+charged raw dead j=j at count
    rw [l,r] at new size
    refine ⟨?_,?_⟩
    · intro i hi
      by_cases e : i=m+j
      · subst i; exact new.trans (dense j (by omega)).symm
      · exact (congrArg Option.isNone (old i e)).trans (agree i (by omega))
    · rw [charged_succ]
      change (advance p m n j _).size+(_+_)=_
      change (advance p m n j _).size+(if lost raw dead j then 1 else 0)=p.size+1 at size
      dsimp only [p] at size count ⊢
      omega

#print axioms literal_correct
#print axioms literal_counts
end IncidenceZeroRestriction
