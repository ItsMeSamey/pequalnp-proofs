import IncidenceLiteralPrefix
import IncidenceForwardPins
namespace IncidenceRouteAlias
open CircuitRewire IncidenceZeroRestriction IncidenceForwardPins IncidenceLiteralPrefix

theorem back (m n s : ℕ) (g : ℕ→Gate) (init : ℕ→Option ℕ) (z : ℕ→Bool)
    (ord : ∀j<s,OrderedBinary (g j) (m+j))
    (refs : ∀w<m+s,((compileLiteral m n g init s).refs w).isNone=z w)
    {p t : Pin} (small : t.1<s) (step : predPin m g z t=some p) :
    p.1<t.1 ∧ (compileLiteral m n g init s).refs (readPin g t)=
      (compileLiteral m n g init s).refs (readPin g p) := by
  let P := compileLiteral m n g init s
  have bo : readPin g t<m+t.1 := by
    obtain ⟨a,b,_⟩ := ord _ small
    unfold readPin
    split <;> assumption
  unfold predPin at step
  dsimp only at step
  split at step
  · contradiction
  rename_i big
  split at step
  · rename_i mode
    let j := readPin g t-m
    have id : readPin g t=m+j := by dsimp [j]; omega
    have old : j<t.1 := by omega
    have js := old.trans small
    have co := ord j js
    have l := refs (g j).left (by have := co.1; omega)
    have r := refs (g j).right (by have := co.2.1; omega)
    have op : (g j).op=.join := mode.1
    have diff : (P.refs (g j).left).isNone ≠ (P.refs (g j).right).isNone :=
      fun h=>mode.2 (l.symm.trans (h.trans r))
    have eq := alias_high m n g init js co op diff
    change P.refs (m+j)=P.refs (pin (g j) (P.refs (g j).left).isNone) at eq
    rw [l] at eq
    have who : (j,z (g j).left)=p := Option.some.inj step
    subst p
    refine ⟨old,?_⟩
    change P.refs (readPin g t)=P.refs (pin (g j) (z (g j).left))
    exact (congrArg P.refs id).trans eq
  · contradiction

theorem along (m n s : ℕ) (g : ℕ→Gate) (init : ℕ→Option ℕ) (z : ℕ→Bool)
    (ord : ∀j<s,OrderedBinary (g j) (m+j))
    (refs : ∀w<m+s,((compileLiteral m n g init s).refs w).isNone=z w)
    {p t : Pin} (route : Route (predPin m g z) p t) (small : t.1<s) :
    (compileLiteral m n g init s).refs (readPin g t)=
      (compileLiteral m n g init s).refs (readPin g p) := by
  induction route with
  | here => rfl
  | next _ step ih =>
    have h := back m n s g init z ord refs small step
    exact h.2.trans (ih (h.1.trans small))

/-- Final compiled reference for every original raw, including a deleted raw. -/
theorem raw_ref (m n s : ℕ) (g : ℕ→Gate) (init : ℕ→Option ℕ) {w : ℕ} (small : w<m) :
    (compileLiteral m n g init s).refs w=init w :=
  (prefix_stable m n g init (Nat.zero_le s)).refs w (by omega)

/-- A terminal which does not emit and has a live socket is genuinely one-zero.
    Its live socket side is recovered from the original dead bits. -/
theorem missing_emit (m n s : ℕ) (g : ℕ→Gate) (init : ℕ→Option ℕ) (z : ℕ→Bool)
    (ord : ∀ j<s,OrderedBinary (g j) (m+j))
    (refs : ∀ w<m+s,((compileLiteral m n g init s).refs w).isNone=z w)
    (t : Pin) (small : t.1<s) (high : z (readPin g t)=false)
    (miss : ¬∃G,stage m n g init t.1=.emit G) :
    z (g t.1).left ≠ z (g t.1).right ∧ t.2=z (g t.1).left := by
  let j := t.1
  let a := compileLiteral m n g init j
  have co := ord j small
  have l := (prefix_stable m n g init small.le).refs _ co.1
  have r := (prefix_stable m n g init small.le).refs _ co.2.1
  have dl : (a.refs (g j).left).isNone=z (g j).left :=
    (congrArg Option.isNone l).symm.trans (refs _ (by have := co.1; omega))
  have dr : (a.refs (g j).right).isNone=z (g j).right :=
    (congrArg Option.isNone r).symm.trans (refs _ (by have := co.2.1; omega))
  have no : ¬∃ G,literal (g j).op (a.refs (g j).left) (a.refs (g j).right)=.emit G := miss
  have hh : (if t.2 then z (g j).right else z (g j).left)=false := by
    cases side : t.2 <;> simpa [j,readPin,side] using high
  change z (g j).left ≠ z (g j).right ∧ t.2=z (g j).left
  rw [←dl,←dr] at hh ⊢
  rcases co.2.2 with op|op <;> cases u : t.2 <;> cases v : a.refs (g j).left <;>
    cases w : a.refs (g j).right <;> simp_all [literal]
#print axioms along
#print axioms missing_emit
end IncidenceRouteAlias
