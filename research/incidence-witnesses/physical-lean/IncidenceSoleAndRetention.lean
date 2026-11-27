import IncidenceSoleReservation
import IncidenceRouteAlias
namespace IncidenceSoleAndRetention
open CircuitRewire IncidenceZeroRestriction IncidenceLiteralPrefix IncidenceRouteAlias
variable {Z : Type*}

def test (X : ℕ → Set Z) (z : Z) (w : ℕ) : Set Unit := (fun _ : Unit=>z) ⁻¹' X w

theorem test_gate (G : Gate) (X : ℕ→Set Z) (y : ℕ) (z : Z) (e : X y=G.eval X) :
    test X z y=G.eval (test X z) := by
  ext u
  cases op : G.op <;> simp [test,e,Gate.eval,op,Op.eval]

theorem reader_nonempty (m s x j o : ℕ) (g : ℕ→Gate) (X : ℕ→Set Z)
    (ord : ∀k<s,OrderedBinary (g k) (m+k)) (sem : ∀k<s,X (m+k)=(g k).eval X)
    (only : ∀k<s,k≠j → (g k).left≠x ∧ (g k).right≠x)
    (out : o<m+s) (internal : o≠x) (a b : Z)
    (agree : ∀i<m,i≠x → (a∈X i ↔ b∈X i)) (on : a∈X o) (off : b∉X o) :
    (X (m+j)).Nonempty := by
  by_contra empty
  have z : X (m+j)=∅ := Set.not_nonempty_iff_eq_empty.mp empty
  have eq := IncidenceSoleReservation.equal_except m s x j g (test X a) (test X b)
    (fun i hi ne=>Set.ext (fun _=>agree i hi ne))
    (fun k hk=>⟨(ord k hk).1,(ord k hk).2.1⟩) only
    (fun k hk=>test_gate _ _ _ _ (sem k hk)) (fun k hk=>test_gate _ _ _ _ (sem k hk))
    (fun _=>by simp [test,z]) o out internal
  exact off ((Set.ext_iff.mp eq ()).mp on)

theorem physical (m n s x j o : ℕ) (g : ℕ→Gate) (init : ℕ→Option ℕ) (X B : ℕ→Set Z)
    (ord : ∀k<s,OrderedBinary (g k) (m+k)) (sem : ∀k<s,X (m+k)=(g k).eval X)
    (bound : ∀w<m,Below n (init w)) (input : ∀w<m,X w=read B (init w))
    (js : j<s) (raw : x<m) (u : ℕ) (kept : init x=some u)
    (kind : (g j).op=.meet) (side : Bool) (reads : pin (g j) side=x)
    (only : ∀k<s,k≠j → (g k).left≠x ∧ (g k).right≠x)
    (out : o<m+s) (internal : o≠x) (a b : Z)
    (agree : ∀i<m,i≠x → (a∈X i ↔ b∈X i)) (on : a∈X o) (off : b∉X o) :
    let P := compileLiteral m n g init s
    ∃k<P.size,(P.code k).op=.meet ∧ pin (P.code k) side=u := by
  let A := compileLiteral m n g init j
  let P := compileLiteral m n g init s
  have present := reader_nonempty m s x j o g X ord sem only out internal a b agree on off
  have old : A.refs (pin (g j) side)=some u := reads ▸ (raw_ref m n j g init raw).trans kept
  obtain ⟨_,_,_,Y,_,_,law⟩ := literal_correct m n s g init X B bound input
    (fun k h=>⟨(ord k h).1,(ord k h).2.1⟩) sem
  have notNone : P.refs (m+j)≠none := by
    intro no
    have z := law _ (show m+j<m+s by omega)
    rw [no] at z
    exact Set.not_nonempty_empty (z ▸ present)
  have emit : ∃G,stage m n g init j=.emit G ∧ G.op=.meet := by
    change ∃G,literal (g j).op (A.refs (g j).left) (A.refs (g j).right)=.emit G ∧ G.op=.meet
    have no : literal (g j).op (A.refs (g j).left) (A.refs (g j).right) ≠ .reuse none :=
      fun e=>notNone (forwarded m n g init js e)
    cases l : A.refs (g j).left <;> cases r : A.refs (g j).right <;> simp_all [literal]
  obtain ⟨G,em,meet⟩ := emit
  have c := emitted m n g init js em
  have p := pinned_emit m n g init js side em old
  exact ⟨A.size,c.1,c.2.1 ▸ meet,p.2⟩
#print axioms physical
end IncidenceSoleAndRetention
