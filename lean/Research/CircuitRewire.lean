import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Prod

namespace CircuitRewire

inductive Op
  | join | meet | copy | zero
  deriving DecidableEq

structure Gate where
  op : Op
  left : ℕ
  right : ℕ

def Op.eval {Z : Type*} : Op → Set Z → Set Z → Set Z
  | .join, x, y => x ∪ y
  | .meet, x, y => x ∩ y
  | .copy, x, _ => x
  | .zero, _, _ => ∅

def Gate.eval {Z : Type*} (g : Gate) (X : ℕ → Set Z) :=
  g.op.eval (X g.left) (X g.right)

def read {Z : Type*} (Y : ℕ → Set Z) : Option ℕ → Set Z
  | none => ∅
  | some i => Y i

def Below (n : ℕ) (r : Option ℕ) := ∀ j, r = some j → j < n

inductive Action
  | reuse (r : Option ℕ)
  | emit (gate : Gate)

def combine (op : Op) (l r : Option ℕ) : Action :=
  match op, l, r with
  | .zero, _, _ => .reuse none
  | .copy, p, _ => .reuse p
  | .join, none, p | .join, p, none => .reuse p
  | .meet, none, _ | .meet, _, none => .reuse none
  | op, some a, some b =>
      if a = b then .reuse (some a) else .emit ⟨op,a,b⟩

def Action.eval {Z : Type*} (Y : ℕ → Set Z) : Action → Set Z
  | .reuse r => read Y r
  | .emit g => g.eval Y

theorem combine_eval {Z : Type*} (Y : ℕ → Set Z) (op : Op) (l r : Option ℕ) :
    (combine op l r).eval Y = op.eval (read Y l) (read Y r) := by
  cases op <;> cases l <;> cases r <;> simp [combine, Action.eval, read, Gate.eval, Op.eval]
  all_goals rename_i a b; by_cases h : a=b <;> simp [h]

theorem reuse_from {op l r t} (h : combine op l r = .reuse t) :
    t = none ∨ t = l ∨ t = r := by
  cases op <;> cases l <;> cases r <;> simp_all [combine]
  all_goals split at h <;> simp_all

theorem emit_from {op l r g} (h : combine op l r = .emit g) :
    l = some g.left ∧ r = some g.right ∧ g.left ≠ g.right ∧ (g.op = .join ∨ g.op = .meet) := by
  cases op <;> cases l <;> cases r <;> simp_all [combine]
  all_goals split at h <;> simp_all
  all_goals subst g; simp_all

def put {α : Type*} (f : ℕ → α) (i : ℕ) (v : α) (j : ℕ) : α := if j=i then v else f j

structure Program where
  size : ℕ
  code : ℕ → Gate
  refs : ℕ → Option ℕ

def advance (p : Program) (m n k : ℕ) : Action → Program
  | .reuse r => {p with refs := put p.refs (m+k) r}
  | .emit g => ⟨p.size+1,put p.code p.size g,put p.refs (m+k) (some (n+p.size))⟩

def compile (m n : ℕ) (raw : ℕ → Gate) (initial : ℕ → Option ℕ) : ℕ → Program
  | 0 => ⟨0, fun _ => ⟨.zero,0,0⟩, initial⟩
  | k+1 =>
    let prev := compile m n raw initial k
    let gate := raw k
    advance prev m n k (combine gate.op (prev.refs gate.left) (prev.refs gate.right))

def Normal (g : Gate) (k : ℕ) := g.left < k ∧ g.right < k ∧ g.left ≠ g.right ∧
    (g.op = .join ∨ g.op = .meet)

def Correct {Z : Type*} (m n k : ℕ) (X B : ℕ → Set Z) (initial : ℕ → Option ℕ)
    (p : Program) : Prop :=
  (∀ j < m, p.refs j = initial j) ∧
  (∀ j < m+k, Below (n+p.size) (p.refs j)) ∧
  (∀ g < p.size, Normal (p.code g) (n+g)) ∧
  ∃ Y : ℕ → Set Z, (∀ j < n, Y j = B j) ∧
    (∀ g < p.size, Y (n+g) = (p.code g).eval Y) ∧
    ∀ j < m+k, X j = read Y (p.refs j)

private theorem oldRead {Z : Type*} (Y : ℕ → Set Z) (i : ℕ) (val : Set Z) (r : Option ℕ)
    (hr : Below i r) : read (put Y i val) r = read Y r := by
  cases r with
  | none => rfl
  | some j => exact ite_eq_right (Nat.ne_of_lt (hr j rfl))

private theorem oldGate {Z : Type*} (Y : ℕ → Set Z) (i : ℕ) (val : Set Z) (g : Gate)
    (ha : g.left < i) (hb : g.right < i) : g.eval (put Y i val) = g.eval Y := by
  simp [Gate.eval,put,Nat.ne_of_lt ha,Nat.ne_of_lt hb]

theorem compile_correct {Z : Type*} (m n s : ℕ) (raw : ℕ → Gate)
    (initial : ℕ → Option ℕ) (X B : ℕ → Set Z)
    (bound : ∀ j < m, Below n (initial j))
    (input : ∀ j < m, X j = read B (initial j))
    (ordered : ∀ g < s, (raw g).left < m+g ∧ (raw g).right < m+g)
    (sem : ∀ g < s, X (m+g) = (raw g).eval X) :
    Correct m n s X B initial (compile m n raw initial s) := by
  induction s with
  | zero =>
    exact ⟨fun _ _ => rfl,bound,fun _ h => by simp [compile] at h,B,fun _ _ => rfl,fun _ h => by simp [compile] at h,input⟩
  | succ k ih =>
    let p := compile m n raw initial k
    obtain ⟨ini,prevBound,prevNorm,Y,hY,hG,hR⟩ := ih
      (fun g hg => ordered g (by omega)) (fun g hg => sem g (by omega))
    change (∀ j < m, p.refs j = initial j) at ini
    change (∀ j < m+k, Below (n+p.size) (p.refs j)) at prevBound
    change (∀ g < p.size, Normal (p.code g) (n+g)) at prevNorm
    change (∀ g < p.size, Y (n+g) = (p.code g).eval Y) at hG
    change (∀ j < m+k, X j = read Y (p.refs j)) at hR
    have ord := ordered k (by omega)
    let act := combine (raw k).op (p.refs (raw k).left) (p.refs (raw k).right)
    have eq : X (m+k) = act.eval Y := by
      rw [sem k (by omega)]
      unfold Gate.eval
      rw [hR _ ord.1,hR _ ord.2]
      exact (combine_eval _ _ _ _).symm
    change Correct m n (k+1) X B initial (advance p m n k act)
    cases e : act with
    | reuse r =>
      simp only [advance]
      have rr := reuse_from (show combine _ _ _ = .reuse r from e)
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
      obtain ⟨fl,fr,ne,binary⟩ := emit_from (show combine _ _ _ = .emit g from e)
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
        · subst h; simpa [put,Normal] using (show Normal g (n+p.size) from ⟨left,right,ne,binary⟩)
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
        · subst j; simpa [put,read,Y',val,e,Action.eval] using eq
        · have lt : j<m+k := by omega
          change X j = read Y' (put p.refs (m+k) (some (n+p.size)) j)
          rw [show put p.refs (m+k) (some (n+p.size)) j = _ from ite_eq_right same]
          exact (hR j lt).trans (oldRead Y _ val _ (prevBound j lt)).symm

theorem original_ref (m n : ℕ) (raw : ℕ → Gate) (initial : ℕ → Option ℕ) (k i : ℕ) (hi : i < m) :
    (compile m n raw initial k).refs i = initial i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [compile,advance]
    split <;> simpa [put,show i ≠ m+k by omega] using ih

def uses (raw : ℕ → Gate) (i k : ℕ) : Prop := (raw k).left = i ∨ (raw k).right = i

instance (raw : ℕ → Gate) (i k : ℕ) : Decidable (uses raw i k) := by
  unfold uses
  infer_instance

theorem gate_count (m n s : ℕ) (raw : ℕ → Gate) (initial : ℕ → Option ℕ)
    (i : ℕ) (hi : i < m) (fixed : initial i = none) :
    (compile m n raw initial s).size + ((Finset.range s).filter (uses raw i)).card ≤ s := by
  induction s with
  | zero => simp [compile]
  | succ k ih =>
    let p := compile m n raw initial k
    let act := combine (raw k).op (p.refs (raw k).left) (p.refs (raw k).right)
    change (advance p m n k act).size + _ ≤ _
    change p.size + _ ≤ k at ih
    have base : p.refs i = none := (original_ref m n raw initial k i hi).trans fixed
    have outside : k ∉ (Finset.range k).filter (uses raw i) := by simp
    rw [Finset.range_add_one,Finset.filter_insert]
    cases e : act with
    | reuse r =>
      by_cases used : uses raw i k <;> simp [advance,used,outside] <;> omega
    | emit g =>
      obtain ⟨fl,fr,_⟩ := emit_from (show combine _ _ _ = .emit g from e)
      have unused : ¬ uses raw i k := by
        rintro (a|b)
        · rw [a,base] at fl; contradiction
        · rw [b,base] at fr; contradiction
      simp [advance,unused]
      omega

def drop (i j : ℕ) : Option ℕ := if j = i then none else some j

theorem restrict_one {Z : Type*} (m s o i : ℕ) (raw : ℕ → Gate) (X : ℕ → Set Z)
    (hi : i < m) (ho : o < m+s) (fixed : X i = ∅) (live : (X o).Nonempty)
    (ordered : ∀ g < s, (raw g).left < m+g ∧ (raw g).right < m+g)
    (sem : ∀ g < s, X (m+g) = (raw g).eval X) :
    ∃ (t out : ℕ) (code : ℕ → Gate) (Y : ℕ → Set Z),
      t + ((Finset.range s).filter (uses raw i)).card ≤ s ∧
      out < m+t ∧ X o = Y out ∧ (∀ j < m, Y j = X j) ∧
      ∀ g < t, Normal (code g) (m+g) ∧ Y (m+g) = (code g).eval Y := by
  let p := compile m m raw (drop i) s
  obtain ⟨_,bounds,norm,Y,inputs,gates,outputs⟩ := compile_correct m m s raw (drop i) X X
    (by intro j hj v e; by_cases h : j=i <;> simp [drop,h] at e; omega)
    (by intro j hj; by_cases h : j=i <;> simp_all [drop,read]) ordered sem
  have eq := outputs o ho
  cases ref : p.refs o with
  | none =>
    change X o = read Y (p.refs o) at eq
    rw [ref] at eq
    exact False.elim ((Set.nonempty_iff_ne_empty.mp live) eq)
  | some out =>
    change X o = read Y (p.refs o) at eq
    rw [ref] at eq
    exact ⟨p.size,out,p.code,Y,gate_count m m s raw (drop i) i hi (by simp [drop]),
      bounds o ho out ref,eq,inputs,fun g hg => ⟨norm g hg,gates g hg⟩⟩

theorem compile_avoids (m n s i : ℕ) (raw : ℕ → Gate) (initial : ℕ → Option ℕ)
    (hi : i < n) (absent : ∀ j < m, initial j ≠ some i)
    (ordered : ∀ g < s, (raw g).left < m+g ∧ (raw g).right < m+g) :
    let p := compile m n raw initial s
    (∀ j < m+s, p.refs j ≠ some i) ∧
    ∀ g < p.size, (p.code g).left ≠ i ∧ (p.code g).right ≠ i := by
  induction s with
  | zero => exact ⟨absent, fun _ h => by simp [compile] at h⟩
  | succ k ih =>
    let p := compile m n raw initial k
    obtain ⟨oldRef,oldCode⟩ := ih (fun g hg => ordered g (by omega))
    change ∀ j < m+k, p.refs j ≠ some i at oldRef
    change ∀ g < p.size, (p.code g).left ≠ i ∧ (p.code g).right ≠ i at oldCode
    have ord := ordered k (by omega)
    let act := combine (raw k).op (p.refs (raw k).left) (p.refs (raw k).right)
    change (∀ j < m+(k+1), (advance p m n k act).refs j ≠ some i) ∧ _
    cases e : act with
    | reuse r =>
      have rr := reuse_from (show combine _ _ _ = .reuse r from e)
      have ok : r ≠ some i := by
        rcases rr with rfl|rfl|rfl
        · simp
        · exact oldRef _ ord.1
        · exact oldRef _ ord.2
      refine ⟨?_,?_⟩
      · intro j hj
        by_cases eq : j=m+k
        · simpa [advance,put,eq] using ok
        · simpa [advance,put,eq] using oldRef j (by omega)
      · change ∀ h < (advance p m n k act).size, ((advance p m n k act).code h).left ≠ i ∧
          ((advance p m n k act).code h).right ≠ i
        rw [e]; exact oldCode
    | emit g =>
      obtain ⟨fl,fr,_⟩ := emit_from (show combine _ _ _ = .emit g from e)
      have nl : g.left ≠ i := fun h => oldRef _ ord.1 (h ▸ fl)
      have nr : g.right ≠ i := fun h => oldRef _ ord.2 (h ▸ fr)
      refine ⟨?_,?_⟩
      · intro j hj
        by_cases eq : j=m+k
        · simp [advance,put,eq,show n+p.size ≠ i by omega]
        · simpa [advance,put,eq] using oldRef j (by omega)
      · change ∀ h < (advance p m n k act).size, ((advance p m n k act).code h).left ≠ i ∧
          ((advance p m n k act).code h).right ≠ i
        rw [e]
        intro h hh
        by_cases eq : h=p.size
        · simpa [advance,put,eq] using And.intro nl nr
        · change h < p.size+1 at hh
          simpa [advance,put,eq] using oldCode h (by omega)

def mask (D : Finset ℕ) (j : ℕ) : Option ℕ := if j ∈ D then none else some j

theorem compile_size (m n s : ℕ) (raw : ℕ → Gate) (initial : ℕ → Option ℕ) :
    (compile m n raw initial s).size ≤ s := by
  induction s with
  | zero => rfl
  | succ k ih =>
    simp only [compile,advance]
    split <;> dsimp <;> omega

theorem restrict_mask {Z : Type*} (m s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set Z)
    (D : Finset ℕ) (ho : o < m+s) (fixed : ∀ j ∈ D, j < m → X j = ∅) (live : (X o).Nonempty)
    (ordered : ∀ g < s, (raw g).left < m+g ∧ (raw g).right < m+g)
    (sem : ∀ g < s, X (m+g) = (raw g).eval X) :
    ∃ (t out : ℕ) (code : ℕ → Gate) (Y : ℕ → Set Z),
      t ≤ s ∧ (∀ i ∈ D, i < m → t + ((Finset.range s).filter (uses raw i)).card ≤ s) ∧
      out < m+t ∧ X o = Y out ∧ (∀ j < m, Y j = X j) ∧
      ∀ g < t, Normal (code g) (m+g) ∧ Y (m+g) = (code g).eval Y ∧
        ∀ i ∈ D, i < m → (code g).left ≠ i ∧ (code g).right ≠ i := by
  let p := compile m m raw (mask D) s
  obtain ⟨_,bounds,norm,Y,inputs,gates,outputs⟩ := compile_correct m m s raw (mask D) X X
    (by intro j hj v e; by_cases h : j ∈ D <;> simp [mask,h] at e; omega)
    (by intro j hj; by_cases h : j ∈ D
        · simpa [mask,h,read] using fixed j h hj
        · simp [mask,h,read]) ordered sem
  have eq := outputs o ho
  cases ref : p.refs o with
  | none =>
    change X o = read Y (p.refs o) at eq
    rw [ref] at eq
    exact False.elim ((Set.nonempty_iff_ne_empty.mp live) eq)
  | some out =>
    change X o = read Y (p.refs o) at eq
    rw [ref] at eq
    refine ⟨p.size,out,p.code,Y,compile_size _ _ _ _ _,?_,bounds o ho out ref,eq,inputs,?_⟩
    · intro i hD hi
      exact gate_count _ _ _ _ _ i hi (by simp [mask,hD])
    · intro g hg
      refine ⟨norm g hg,gates g hg,?_⟩
      intro i hD hi
      apply (compile_avoids m m s i raw (mask D) hi ?_ ordered).2 g hg
      intro j _
      by_cases h : j ∈ D
      · simp [mask,h]
      · have ne : j ≠ i := fun e => h (e ▸ hD)
        simp [mask,h,ne]

theorem preimage_gate {Z W : Type*} (f : W → Z) (g : Gate) (X : ℕ → Set Z) :
    f ⁻¹' (g.eval X) = g.eval (fun j => f ⁻¹' X j) := by
  cases g with
  | mk op a b => cases op <;> rfl

theorem select_gates {Z : Type*} (m s : ℕ) (X : ℕ → Set Z)
    (steps : ∀ k < s, ∃ a < m+k, ∃ b < m+k,
      X (m+k) = X a ∪ X b ∨ X (m+k) = X a ∨ X (m+k) = ∅ ∨ X (m+k) = X a ∩ X b) :
    ∃ raw : ℕ → Gate, (∀ k < s, (raw k).left < m+k ∧ (raw k).right < m+k) ∧
      ∀ k < s, X (m+k) = (raw k).eval X := by
  classical
  have get (k : ℕ) (hk : k < s) : ∃ g : Gate,
      g.left < m+k ∧ g.right < m+k ∧ X (m+k) = g.eval X := by
    obtain ⟨a,ha,b,hb,law⟩ := steps k hk
    rcases law with u|c|z|i
    · exact ⟨⟨.join,a,b⟩,ha,hb,u⟩
    · exact ⟨⟨.copy,a,b⟩,ha,hb,c⟩
    · exact ⟨⟨.zero,a,b⟩,ha,hb,z⟩
    · exact ⟨⟨.meet,a,b⟩,ha,hb,i⟩
  let raw (k : ℕ) : Gate := if h : k<s then (get k h).choose else ⟨.zero,0,0⟩
  refine ⟨raw,?_,?_⟩
  · intro k hk
    simpa [raw,hk] using And.intro (get k hk).choose_spec.1 (get k hk).choose_spec.2.1
  · intro k hk
    simpa [raw,hk] using (get k hk).choose_spec.2.2

end CircuitRewire
