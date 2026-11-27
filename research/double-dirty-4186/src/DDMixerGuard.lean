import DDMixerRoot

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

noncomputable abbrev splitSlot (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (m w : ℕ) := physicalSlot n C (splitCuts n C (orT G C) m) C.size w

private theorem kept_top {t : ℕ} (ht : t ∈ tops G C) : Kept G C (n+t) := by
  intro j hj eq
  have jt : j=t := by omega
  subst j
  exact GateOp.noConfusion ((Finset.mem_filter.mp ht).2.1.symm.trans (Finset.mem_filter.mp hj).2.1)

private theorem top_agree {m t : ℕ} (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : t ∈ tops G C)
    (x : Fin n → Bool) (on : Influence n C m (n+t) → gateVal n C m x = true) :
    gateVal n C t x = denotation (splitSlot G C m (n+t)) x := by
  have bound := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  exact root_cofactor G C m edge least form true (w := n+t) (by change n+t<n+C.gates.length; omega)
    (kept_top ht) x on

theorem split_guard_real {m t : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (ht : t ∈ tops G C) (path : Influence n C m (n+t)) :
    ∃ W : Signal n, splitSlot G C m (n+t) = some W ∧ ∀ x,
      gateVal n C t x = (gateVal n C m x && W x) := by
  have sem (x : Fin n → Bool) :
      gateVal n C t x = (gateVal n C m x && denotation (splitSlot G C m (n+t)) x) := by
    cases hv : gateVal n C m x with
    | true => simpa only [Bool.true_and] using top_agree edge least form ht x (fun _ => hv)
    | false =>
      rw [Bool.false_and]
      cases htval : gateVal n C t x with
      | false => rfl
      | true =>
        have h : gateVal n C m x = true :=
          mixer_dominates_top G C m D edge least form t ht path x htval
        simp_all
  cases hslot : splitSlot G C m (n+t) with
  | none =>
    exfalso
    apply (mixer_info D).2.2
    intro x hx
    have htx := sem x
    simp [hslot,denotation,hx] at htx
    exact (Finset.mem_filter.mp ht).2.2 x htx
  | some W =>
    refine ⟨W,rfl,?_⟩
    intro x
    simpa [hslot,denotation] using sem x

theorem unchanged_top_slot {m t : ℕ} (_D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : t ∈ tops G C)
    (unaffected : ¬Influence n C m (n+t)) : splitSlot G C m (n+t) = some (gateVal n C t) := by
  have sem (x : Fin n → Bool) := top_agree edge least form ht x (fun h => (unaffected h).elim)
  cases s : splitSlot G C m (n+t) with
  | none =>
    have h := sem (fun _ => false)
    have b := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have z : gateVal n C t (fun _ => false) = false :=
      zero_wire C least.1 _ (by change n+t < n+C.gates.length; omega)
    simp [s,denotation,z] at h
  | some f =>
    exact congrArg some (funext fun x => (by simpa [s,denotation] using (sem x).symm))

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
