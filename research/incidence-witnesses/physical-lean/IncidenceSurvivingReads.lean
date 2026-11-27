import IncidenceRouteAlias
namespace IncidenceSurvivingReads
open CircuitRewire IncidenceZeroRestriction IncidenceForwardPins IncidenceLiteralPrefix IncidenceRouteAlias
open scoped BigOperators
theorem sum_losses {W : Type*} [DecidableEq W] (labels : Finset W)
    (start keep : Finset Pin) (before after : Pin → W) (allowed : Finset ℕ)
    (survives : Pin → Bool) (finish : Pin → Pin) (bill : Pin → ℕ)
    (toKeep : ∀p∈start,survives p=true → finish p∈keep ∧ after (finish p)=before p)
    (injKeep : Set.InjOn finish (↑(start.filter (fun p=>survives p=true)) : Set Pin))
    (toBill : ∀p∈start,survives p=false → bill p∈allowed)
    (injBill : Set.InjOn bill (↑(start.filter (fun p=>survives p=false)) : Set Pin))
    (inLabels : ∀p∈start,before p∈labels) :
    (∑ w∈labels, ((start.filter (fun p=>before p=w)).card -
        (keep.filter (fun p=>after p=w)).card)) ≤ allowed.card := by
  classical
  let lost := start.filter (fun p=>survives p=false)
  have step (w : W) :
      (start.filter (fun p=>before p=w)).card - (keep.filter (fun p=>after p=w)).card
        ≤ (lost.filter (fun p=>before p=w)).card := by
    let A := start.filter (fun p=>before p=w)
    have bound : (A.filter (fun p=>survives p=true)).card ≤
        (keep.filter (fun p=>after p=w)).card := by
      apply Finset.card_le_card_of_injOn finish
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨ha,yes⟩
        rcases Finset.mem_filter.mp ha with ⟨hs,lw⟩
        obtain ⟨kin,keq⟩ := toKeep p hs yes
        exact Finset.mem_filter.mpr ⟨kin,keq.trans lw⟩
      · apply injKeep.mono
        intro p hp
        obtain ⟨ha,y⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,y⟩
    have pos := Finset.card_filter_add_card_filter_not (s:=A) (fun p=>survives p=true)
    have lf : A.filter (fun p=>¬survives p=true) = lost.filter (fun p=>before p=w) := by
      ext p
      cases h : survives p <;> simp [A,lost,h,and_comm,and_left_comm]
    rw [lf] at pos
    change A.card - _ ≤ _
    omega
  calc
    _ ≤ ∑ w∈labels, (lost.filter (fun p=>before p=w)).card := Finset.sum_le_sum (fun w _=>step w)
    _ = lost.card := by
      have ht : ∀p∈lost,before p∈labels := fun p hp=>inLabels p (Finset.mem_filter.mp hp).1
      simpa using (Finset.sum_fiberwise_of_maps_to ht (fun _ : Pin=> (1 : ℕ)))
    _ ≤ _ := Finset.card_le_card_of_injOn bill
      (fun p hp=>toBill p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2) injBill

def pins (s : ℕ) : Finset Pin := (Finset.range s) ×ˢ (Finset.univ : Finset Bool)
theorem mem_pins (p : Pin) (s : ℕ) : p∈pins s ↔ p.1<s := by simp [pins]

def starts (m s : ℕ) (g : ℕ→Gate) (init : ℕ→Option ℕ) : Finset Pin :=
  (pins s).filter (fun p=>readPin g p<m ∧ (init (readPin g p)).isSome)

def surplus (s : ℕ) (g : ℕ→Gate) (z : ℕ→Bool) (comp : Finset ℕ) :=
  (Finset.range s).filter (fun j=>(g j).op=.meet ∧ z (g j).left ≠ z (g j).right ∧ j∉comp)

theorem physical (m n s o : ℕ) (g : ℕ→Gate) (init : ℕ→Option ℕ) (z : ℕ→Bool)
    (ord : ∀j<s,OrderedBinary (g j) (m+j))
    (rawDark : ∀w<m,(init w).isNone=z w)
    (dense : ∀j<s,z (m+j)=deadOut (g j).op (z (g j).left) (z (g j).right))
    (bound : ∀w<m,Below n (init w))
    (live : ∀j<s,j≠o → ∃q : Pin,j<q.1 ∧ q.1<s ∧ readPin g q=m+j)
    (X : ℕ→Set ℕ) (input : ∀w<m,X w=read (fun x : ℕ=>({x} : Set ℕ)) (init w))
    (gate : ∀j<s,X (m+j)=(g j).eval X)
    (reject : ∀x<n,x∉X (m+o))
    (comp : Finset ℕ) (wide : ∀j∈comp, ∃a b : ℕ, a≠b ∧
      a∈X (readPin g (j,z (g j).left)) ∧ b∈X (readPin g (j,z (g j).left))) :
    let P := compileLiteral m n g init s
    (∑ x∈Finset.range n, (((starts m s g init).filter
      (fun p=>(init (readPin g p)).getD 0=x)).card -
      ((pins P.size).filter (fun p=>readPin P.code p=x)).card)) ≤ (surplus s g z comp).card := by
  classical
  let P := compileLiteral m n g init s
  let S := starts m s g init
  let key := fun p=> (init (readPin g p)).getD 0
  have src (p : Pin) (hp : p∈S) : p.1<s ∧ readPin g p<m ∧ init (readPin g p)=some (key p) := by
    rcases Finset.mem_filter.mp hp with ⟨a,b,c⟩
    refine ⟨(mem_pins p s).mp a,b,?_⟩
    cases e : init (readPin g p) <;> simp_all [key]
  have dz (j : ℕ) (hj : j<s) : z (m+j)=IncidenceOperandLedger.zeroAt z (g j) := by
    rw [dense j hj]
    cases op : (g j).op <;> simp [deadOut,IncidenceOperandLedger.zeroAt,op]
  have refs := (literal_counts m n s g init z rawDark ord dense).1
  obtain ⟨_,_,_,Y,ys,_,val⟩ := literal_correct m n s g init X
    (fun x : ℕ=>({x} : Set ℕ)) bound input (fun j h=>⟨(ord j h).1,(ord j h).2.1⟩) gate
  have one {w x : ℕ} (h : w<m+s) (rx : P.refs w=some x) (nx : x<n) : X w={x} := by
    rw [val w h,rx]; exact ys x nx
  have high (p : Pin) (hp : p∈S) : z (readPin g p)=false := by
    rw [←rawDark _ (src p hp).2.1,(src p hp).2.2]; rfl
  have routes (p : Pin) (hp : p∈S) := live_route m s o g z live dz p (src p hp).1 (high p hp)
  let T := fun p=> if h : p∈S then Classical.choose (routes p h) else p
  have tr (p : Pin) (hp : p∈S) : Route (predPin m g z) p (T p) ∧ (T p).1<s ∧
      z (readPin g (T p))=false ∧ (¬bypass g z (T p).1 ∨ (T p).1=o) := by
    simpa [T,hp] using Classical.choose_spec (routes p hp)
  have inj := terminal_injective m g z S (fun p hp=>(src p hp).2.1) T (fun p hp=>(tr p hp).1)
  let E := fun j=>∃H,stage m n g init j=.emit H
  let stay := fun p=>decide (E (T p).1)
  let finish := fun p=>((compileLiteral m n g init (T p).1).size,(T p).2)
  have pinRef (p : Pin) (hp : p∈S) : P.refs (readPin g (T p))=some (key p) :=
    ((along m n s g init z ord refs (tr p hp).1 (tr p hp).2.1).trans
      (raw_ref m n s g init (src p hp).2.1)).trans (src p hp).2.2
  have lim (p : Pin) (hp : p∈S) : key p<n := bound _ (src p hp).2.1 _ (src p hp).2.2
  have earlier (p : Pin) (hp : p∈S) : readPin g (T p)<m+(T p).1 := by
    have a := ord _ (tr p hp).2.1
    unfold readPin; split <;> first | exact a.1 | exact a.2.1
  have loss (p : Pin) (hp : p∈S) (no : ¬E (T p).1) :
      (T p).1∈surplus s g z comp ∧ (T p).2=z (g (T p).1).left := by
    let t := T p
    obtain ⟨_,small,hi,last⟩ := tr p hp
    obtain ⟨diff,side⟩ := missing_emit m n s g init z ord refs t small hi no
    change t.1<s at small
    have refx := pinRef p hp
    have bad : (g t.1).op≠.join := by
      intro op
      have bypassed : bypass g z t.1 := ⟨op,diff⟩
      have isOut : t.1=o := last.resolve_left (fun h=>h bypassed)
      have ll := refs (g t.1).left ((ord t.1 small).1.trans (Nat.add_lt_add_left small m))
      have rr := refs (g t.1).right ((ord t.1 small).2.1.trans (Nat.add_lt_add_left small m))
      have e := alias_high m n g init small (ord t.1 small) op
        (fun h=>diff (ll.symm.trans (h.trans rr)))
      change P.refs (m+t.1)=P.refs (pin (g t.1) (P.refs (g t.1).left).isNone) at e
      change (P.refs (g t.1).left).isNone=z (g t.1).left at ll
      rw [ll,←side] at e
      have root : P.refs (m+t.1)=some (key p) := e.trans refx
      have supply := one (Nat.add_lt_add_left small m) root (lim p hp)
      have accepted : key p∈X (m+t.1) := supply ▸ Set.mem_singleton _
      exact reject _ (lim p hp) (isOut ▸ accepted)
    have meet := (ord t.1 small).2.2.resolve_left bad
    have notComp : t.1∉comp := by
      intro hc
      obtain ⟨a,b,ab,ha,hb⟩ := wide _ hc
      have pt : (t.1,z (g t.1).left)=t := by rw [←side]
      have w := earlier p hp
      have tx := one (w.trans (Nat.add_lt_add_left small m)) refx (lim p hp)
      rw [pt,tx] at ha hb
      exact ab ((Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm)
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr small,meet,diff,notComp⟩,side⟩
  apply sum_losses (Finset.range n) S (pins P.size) key (readPin P.code) (surplus s g z comp)
    stay finish (fun p=>(T p).1)
  · intro p hp st
    obtain ⟨G,em⟩ : E (T p).1 := of_decide_eq_true st
    have near := (prefix_stable m n g init (tr p hp).2.1.le).refs _ (earlier p hp)
    have px := near.symm.trans (pinRef p hp)
    have keep := pinned_emit m n g init (tr p hp).2.1 (T p).2 em px
    exact ⟨(mem_pins _ _).mpr keep.1,keep.2⟩
  · intro p hp q hq eq
    rcases Finset.mem_filter.mp hp with ⟨pS,ps⟩
    rcases Finset.mem_filter.mp hq with ⟨qS,qs⟩
    apply inj pS qS
    have sideEq : (finish p).2=(finish q).2 := congrArg Prod.snd eq
    exact Prod.ext (emitted_injective m n g init (of_decide_eq_true ps)
      (of_decide_eq_true qs) (congrArg Prod.fst eq)) sideEq
  · intro p hp st
    exact (loss p hp (of_decide_eq_false st)).1
  · intro p hp q hq eq
    rcases Finset.mem_filter.mp hp with ⟨pS,ps⟩
    rcases Finset.mem_filter.mp hq with ⟨qS,qs⟩
    apply inj pS qS
    change (T p).1=(T q).1 at eq
    apply Prod.ext eq
    rw [(loss p pS (of_decide_eq_false ps)).2,(loss q qS (of_decide_eq_false qs)).2,eq]
  · intro p hp; exact Finset.mem_range.mpr (lim p hp)
#print axioms physical
end IncidenceSurvivingReads
