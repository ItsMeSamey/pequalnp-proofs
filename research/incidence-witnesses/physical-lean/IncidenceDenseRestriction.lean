import IncidenceZeroRestriction

namespace IncidenceZeroRestriction
open CircuitRewire

/-- A wire's dense zero flag, using the actual evaluations at the all-free-true test. -/
noncomputable def zeroAt {Z : Type*} (X : Nat→Set Z) (top : Z) (i : Nat) : Bool := by
  classical exact decide (top∉X i)

theorem zeroAt_step {Z : Type*} (X : Nat→Set Z) (top : Z) (i : Nat) (g : Gate)
    (hg : X i=g.eval X) :
    zeroAt X top i=deadOut g.op (zeroAt X top g.left) (zeroAt X top g.right) := by
  classical
  cases h : g.op <;> by_cases l : top∈X g.left <;> by_cases r : top∈X g.right <;>
    simp [zeroAt,hg,Gate.eval,Op.eval,h,l,r,deadOut]

/-- An actual output in the literal zero minor, its entire truth set, and its exact emitted-row
count before dead trimming or duplicate-operand elimination. Repeated references may remain. -/
theorem dense_minor {Z : Type*} (m n s o : Nat) (raw : Nat→Gate) (init : Nat→Option Nat)
    (X B : Nat→Set Z) (top : Z) (bound : ∀ i<m,Below n (init i))
    (input : ∀ i<m,X i=CircuitRewire.read B (init i)) (ones : ∀ j<n,top∈B j)
    (order : ∀ i<s,OrderedBinary (raw i) (m+i))
    (sem : ∀ i<s,X (m+i)=(raw i).eval X) (out : o<m+s) (present : (X o).Nonempty) :
    let p := compileLiteral m n raw init s
    p.size + charged raw (zeroAt X top) s=s ∧
    (∀ i<p.size,OrderedBinary (p.code i) (n+i)) ∧
    ∃ j<n+p.size,p.refs o=some j ∧ ∃ Y : Nat→Set Z,(∀ i<n,Y i=B i) ∧
      (∀ i<p.size,Y (n+i)=(p.code i).eval Y) ∧ Y j=X o := by
  classical
  let p := compileLiteral m n raw init s
  have dense (i : Nat) (hi : i<m) : (init i).isNone=zeroAt X top i := by
    cases e : init i with
    | none => simp [zeroAt,input i hi,e,CircuitRewire.read]
    | some j =>
      have mem := ones j (bound i hi j e)
      simp [zeroAt,input i hi,e,CircuitRewire.read,mem]
  obtain ⟨_,count⟩ := literal_counts m n s raw init (zeroAt X top) dense order
    (fun i hi=>zeroAt_step X top _ _ (sem i hi))
  obtain ⟨_,bounds,kinds,Y,base,eval,wire⟩ := literal_correct m n s raw init X B bound input
    (fun i hi=>⟨(order i hi).1,(order i hi).2.1⟩) sem
  refine ⟨count,kinds,?_⟩
  have eq : X o=CircuitRewire.read Y (p.refs o) := wire o out
  cases e : p.refs o with
  | none =>
    rw [e] at eq
    exact (Set.not_nonempty_empty (eq ▸ present)).elim
  | some j =>
    rw [e] at eq
    exact ⟨j,bounds o out j e,rfl,Y,base,eval,eq.symm⟩

#print axioms dense_minor
end IncidenceZeroRestriction
