import IncidenceZeroRestriction
namespace IncidenceLiteralPrefix
open CircuitRewire IncidenceZeroRestriction
def stage (m n : ℕ) (raw : ℕ → Gate) (init : ℕ → Option ℕ) (j : ℕ) :=
  let p := compileLiteral m n raw init j
  let g := raw j
  literal g.op (p.refs g.left) (p.refs g.right)

theorem step (m n : ℕ) (raw : ℕ → Gate) (init : ℕ → Option ℕ) (j : ℕ) :
    compileLiteral m n raw init (j+1) =
      advance (compileLiteral m n raw init j) m n j (stage m n raw init j) := rfl

structure Extends (bound : ℕ) (a b : Program) : Prop where
  grows : a.size≤b.size
  code : ∀i<a.size,b.code i=a.code i
  refs : ∀w<bound,b.refs w=a.refs w

theorem single (p : Program) (m n j : ℕ) (a : Action) :
    Extends (m+j) p (advance p m n j a) := by
  cases a <;> constructor <;> simp only [advance]
  all_goals first | exact Nat.le_refl _ | exact Nat.le_succ _ | intro i hi; simp [put,Nat.ne_of_lt hi]

theorem prefix_stable (m n : ℕ) (raw : ℕ → Gate) (init : ℕ → Option ℕ) {j s : ℕ} (le : j≤s) :
    Extends (m+j) (compileLiteral m n raw init j) (compileLiteral m n raw init s) := by
  induction s with
  | zero =>
    have z : j=0 := by omega
    subst j; exact ⟨le_rfl,fun _ _=>rfl,fun _ _=>rfl⟩
  | succ a ih =>
    by_cases eq : j=a+1
    · subst j; exact ⟨le_rfl,fun _ _=>rfl,fun _ _=>rfl⟩
    have prev := ih (show j≤a by omega)
    rw [step m n raw init a]
    have now := single (compileLiteral m n raw init a) m n a (stage m n raw init a)
    exact ⟨prev.grows.trans now.grows,fun i hi=>(now.code i (hi.trans_le prev.grows)).trans (prev.code i hi),
      fun w hw=>(now.refs w (by omega)).trans (prev.refs w hw)⟩

theorem emitted (m n : ℕ) (raw : ℕ → Gate) (init : ℕ → Option ℕ) {j s : ℕ}
    (h : j<s) {G : Gate} (em : stage m n raw init j=.emit G) :
    let a := compileLiteral m n raw init j
    let b := compileLiteral m n raw init s
    a.size<b.size ∧ b.code a.size=G ∧ b.refs (m+j)=some (n+a.size) := by
  let a := compileLiteral m n raw init j
  have pp := prefix_stable m n raw init (show j+1≤s by omega)
  rw [step m n raw init j,em] at pp
  have inc := pp.grows
  change a.size+1≤_ at inc
  refine ⟨inc,?_,?_⟩
  · have c := pp.code a.size (by change a.size<a.size+1; omega)
    simpa [advance,put,a] using c
  · have r := pp.refs (m+j) (by omega)
    simpa [advance,put,a] using r

theorem emitted_injective (m n : ℕ) (raw : ℕ → Gate) (init : ℕ → Option ℕ)
    {i j : ℕ} (a : ∃ G,stage m n raw init i=.emit G)
    (b : ∃ G,stage m n raw init j=.emit G)
    (eq : (compileLiteral m n raw init i).size=(compileLiteral m n raw init j).size) : i=j := by
  obtain ⟨x,hx⟩ := a
  obtain ⟨y,hy⟩ := b
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt|gt
  · have bad := (emitted m n raw init lt hx).1; omega
  · have bad := (emitted m n raw init gt hy).1; omega

theorem forwarded (m n : ℕ) (raw : ℕ → Gate) (init : ℕ → Option ℕ) {j s : ℕ}
    (h : j<s) {a : Option ℕ} (em : stage m n raw init j=.reuse a) :
    (compileLiteral m n raw init s).refs (m+j)=a := by
  have pp := prefix_stable m n raw init (show j+1≤s by omega)
  rw [step m n raw init j,em] at pp
  simpa [advance,put] using pp.refs (m+j) (by omega)

def pin (G : Gate) (side : Bool) : ℕ := if side then G.right else G.left

theorem pinned_emit (m n : ℕ) (raw : ℕ → Gate) (init : ℕ → Option ℕ) {j s x : ℕ}
    (h : j<s) (side : Bool) {G : Gate} (em : stage m n raw init j=.emit G)
    (ref : (compileLiteral m n raw init j).refs (pin (raw j) side)=some x) :
    let a := compileLiteral m n raw init j
    let b := compileLiteral m n raw init s
    a.size<b.size ∧ pin (b.code a.size) side=x := by
  have e := emitted m n raw init h em
  obtain ⟨el,er,_⟩ := literal_emit em
  refine ⟨e.1,?_⟩
  rw [e.2.1]
  cases side <;> simp only [pin,Bool.false_eq_true,ite_false,ite_true] at ref ⊢
  · exact Option.some.inj (el.symm.trans ref)
  · exact Option.some.inj (er.symm.trans ref)

theorem keep_or_forward (G : Gate) (l r : Option ℕ) (normal : G.op=.join ∨ G.op=.meet)
    (side : Bool) {x : ℕ} (active : (if side then r else l)=some x) :
    (∃ H, literal G.op l r=.emit H ∧ pin H side=x) ∨
    (G.op=.join ∧ literal G.op l r=.reuse (some x)) ∨
    (G.op=.meet ∧ literal G.op l r=.reuse none) := by
  obtain h|h := normal <;> cases side <;> cases l <;> cases r <;>
    simp_all [literal,pin]
/-- A kept raw or alias is read at the same operand side in the final emitted row.
    If the gate is bypassed its final reference is the same raw. An absorbing
    gate has no retained raw pin. -/
theorem final_pin (m n : ℕ) (raw : ℕ→Gate) (init : ℕ→Option ℕ)
    {j s x : ℕ} (h : j<s) (side : Bool) (order : OrderedBinary (raw j) (m+j))
    (orig : (compileLiteral m n raw init s).refs (pin (raw j) side)=some x) :
    let a := compileLiteral m n raw init j
    let b := compileLiteral m n raw init s
    (∃G,stage m n raw init j=.emit G ∧ a.size<b.size ∧ pin (b.code a.size) side=x) ∨
    ((raw j).op=.join ∧ b.refs (m+j)=some x) ∨
    ((raw j).op=.meet ∧ b.refs (m+j)=none) := by
  let a := compileLiteral m n raw init j
  have ord : pin (raw j) side < m+j := by cases side <;> first | exact order.1 | exact order.2.1
  have old : a.refs (pin (raw j) side)=some x :=
    ((prefix_stable m n raw init h.le).refs _ ord).symm.trans orig
  have active : (if side then a.refs (raw j).right else a.refs (raw j).left)=some x := by
    cases side <;> exact old
  rcases keep_or_forward (raw j) (a.refs (raw j).left) (a.refs (raw j).right)
    order.2.2 side active with ⟨G,em,eq⟩ | ⟨op,re⟩ | ⟨op,re⟩
  · exact Or.inl ⟨G,em,pinned_emit m n raw init h side em old⟩
  · exact Or.inr (Or.inl ⟨op,forwarded m n raw init h re⟩)
  · exact Or.inr (Or.inr ⟨op,forwarded m n raw init h re⟩)

/-- An actual bypass OR forwards the unique live operand's final compiled reference. -/
theorem alias_high (m n : ℕ) (raw : ℕ→Gate) (init : ℕ→Option ℕ) {j s : ℕ}
    (h : j<s) (ord : OrderedBinary (raw j) (m+j)) (op : (raw j).op=.join)
    (diff : ((compileLiteral m n raw init s).refs (raw j).left).isNone ≠
      ((compileLiteral m n raw init s).refs (raw j).right).isNone) :
    let b := compileLiteral m n raw init s
    b.refs (m+j)=b.refs (pin (raw j) ((b.refs (raw j).left).isNone)) := by
  let a := compileLiteral m n raw init j
  let b := compileLiteral m n raw init s
  have pp := prefix_stable m n raw init h.le
  have l : b.refs (raw j).left=a.refs (raw j).left := pp.refs _ ord.1
  have r : b.refs (raw j).right=a.refs (raw j).right := pp.refs _ ord.2.1
  change (b.refs (raw j).left).isNone ≠ (b.refs (raw j).right).isNone at diff
  rw [l,r] at diff
  change b.refs (m+j)=b.refs (pin (raw j) (b.refs (raw j).left).isNone)
  rw [l]
  cases e : a.refs (raw j).left <;> cases f : a.refs (raw j).right
  · simp [e,f] at diff
  · change b.refs (m+j)=b.refs (raw j).right
    rw [r]
    apply forwarded m n raw init h
    change literal (raw j).op (a.refs (raw j).left) (a.refs (raw j).right)=_
    simp [op,e,f,literal]
  · change b.refs (m+j)=b.refs (raw j).left
    rw [l]
    apply forwarded m n raw init h
    change literal (raw j).op (a.refs (raw j).left) (a.refs (raw j).right)=_
    simp [op,e,f,literal]
  · simp [e,f] at diff
#print axioms emitted_injective
#print axioms final_pin
#print axioms alias_high
end IncidenceLiteralPrefix
