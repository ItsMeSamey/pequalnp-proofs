import Q1DoublePrivateEndpoint
import Q1PrivateSignal
import Q1PrivateEnumerate

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux.Q1Double

structure ClauseSignal {n a w : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (term : (Fin n → Bool) → Bool) (A : Fin a → Private.Clause n) (W : Fin w → Private.Clause n) : Prop where
  semantics : ∀ x, term x = true ↔ ∀ c, ∃ v ∈ Private.literals A W c, x v = true
  anchor : ∀ c, ∀ x ∈ Private.literals A W c, ∀ y ∈ Private.literals A W c, x ≠ y →
    ∃ d, ∀ z ∈ Private.literals A W c, G.Adj d z ∧ s(d,z) ∈ starEdges G C

theorem finishPrivateSignals {n a b w H : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (D : Allocation G C) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (one : (orN G C \ lam G C).card = 1) (present : D.pivot ∈ D.components)
    (paid : ∀ i ∈ D.components.erase D.pivot, D.Local i) (res : D.edges D.pivot ⊆ Ustar G C)
    (accepted : D.edges D.pivot ⊆ gammaE G C H) (below : BelowF G C H)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hw : 1 ≤ w)
    (A : Fin a → Private.Clause n) (B : Fin b → Private.Clause n) (W : Fin w → Private.Clause n)
    (left right : (Fin n → Bool) → Bool) (split : ∀ x, gateVal n C H x = (left x || right x))
    (descL : ClauseSignal G C left A W) (descR : ClauseSignal G C right B W)
    (price : a+b+w ≤ D.allowance D.pivot+1) : Positive G C := by
  classical
  obtain ⟨L,R,dis,un,_,lowns,rowns⟩ := partitionProjected (H:=H) G C (D.edges D.pivot) accepted left right split
  have lsub : L ⊆ Ustar G C := by
    intro e he
    apply res
    rw [← un]
    exact Finset.mem_union_left R he
  have rsub : R ⊆ Ustar G C := by
    intro e he
    apply res
    rw [← un]
    exact Finset.mem_union_right L he
  have lclean (x : Fin n → Bool) (h : left x = true) : graphFun G ∅ x = true := by
    apply below x
    rw [split x,h,Bool.true_or]
  have rclean (x : Fin n → Bool) (h : right x = true) : graphFun G ∅ x = true := by
    apply below x
    rw [split x,h,Bool.or_true]
  obtain ⟨P,hP⟩ := Private.batch_of_signal (G:=G) (C:=C) four A W L lsub left lowns lclean descL.semantics descL.anchor
  obtain ⟨Q,hQ⟩ := Private.batch_of_signal (G:=G) (C:=C) four B W R rsub right rowns rclean descR.semantics descR.anchor
  obtain ⟨e,he⟩ := edge
  obtain ⟨p,hp,hq,labels,eq⟩ := Private.concatenate (V:=Fin n) e.out.1 L R (D.edges D.pivot) dis un P.pt Q.pt hP hQ
  exact D.finishPrivate (a:=a) (b:=b) (w:=w) (r:=L.card) (s:=R.card) four ⟨e,he⟩ least form one present paid res
    ha hb hw P Q p hp hq labels eq price

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation
