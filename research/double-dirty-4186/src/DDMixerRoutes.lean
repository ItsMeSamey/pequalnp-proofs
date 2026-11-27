import DDOriginalRouteUnique

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

theorem influence_le {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {g w : ℕ} (p : Influence n C g w) :
    n+g ≤ w := by
  induction p with
  | source => exact le_rfl
  | step _ hj pin ih => exact ih.trans (Nat.le_of_lt (ao.2.1 _ hj _ pin))

theorem kept_forces_bad_reader_pin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) {i j : ℕ} (hi : i<C.size) (hj : j<C.size)
    (pin : n+i ∈ (gateAt C j).inputs) (keep : Kept G C (n+j)) : ¬ BelowF G C i := by
  intro below
  obtain ⟨reader,out,_⟩ := main_real n G C edge least form
  have rd : j∈readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,pin⟩
  have notOut : n+i ≠ C.output := by
    intro e
    have ix : C.output-n = i := by omega
    rw [ix] at out
    simpa [out] using rd
  obtain ⟨r,sing,op,hb⟩ := reader i hi below notOut
  rw [sing,Finset.mem_singleton] at rd
  subst r
  exact keep j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,op,hb⟩) rfl

theorem top_affected_iff_route {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m : ℕ) (double : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) {t : ℕ} (top : t∈tops G C) :
    Influence n C m (n+t) ↔ t ∈ centreless G C ∧ MixerRoute n G C m m t := by
  constructor
  · intro path
    have walk {w : ℕ} (p : Influence n C m w) (keep : Kept G C w) :
        ∃ i, w=n+i ∧ i<C.size ∧ (i=m ∨ (gateAt C i).op=.and) ∧
          (BelowF G C i → i∈centreless G C) ∧
          (∀ t, MixerRoute n G C m i t → MixerRoute n G C m m t) := by
      induction p with
      | source =>
        exact ⟨m,rfl,(mixer_info double).1,Or.inl rfl,
          fun hb => ((mixer_info double).2.2 hb).elim,fun _ h => h⟩
      | @step j w prior hj pin ih =>
        have ge := influence_le least.1 prior
        obtain ⟨i,eq,hi,old,_,lift⟩ := ih (kept_nonclean edge least form hj w keep pin)
        subst w
        have bad := kept_forces_bad_reader_pin G C edge least form hi hj pin keep
        have kind : i=m ∨ i∈junk G C :=
          old.imp_right fun ha => (S4183.junk_iff G C i).mpr ⟨hi,ha,bad⟩
        have noOR : (gateAt C j).op ≠ .or := by
          intro hor
          rcases kind with rfl|junk
          · exact no_mixer_or double least.1 hj pin hor
          · have eq := dirty_or_eq double least.1 junk hj pin hor
            have lt := least.1.2.1 j hj _ pin
            omega
        have hand := (least.1.1 _ (Q0ReaderDeps.S90.gateAt_mem hj)).resolve_right noOR
        have empty : orIn n C (n+i) = ∅ := by
          rcases old with rfl|ha
          · exact mixer_empty double least.1
          · exact Q0.and_empty_support ha
        refine ⟨j,rfl,hj,Or.inr hand,?_,?_⟩
        · intro below
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hand,below⟩,?_⟩
          rcases Q0.reader_pin least.1 hj pin with h|h
          · exact Or.inl (by simpa [side,h] using empty)
          · exact Or.inr (by simpa [side,h] using empty)
        · intro t route
          apply lift t
          have nt : i ∉ centreless G C := fun h => bad (Finset.mem_filter.mp
            ((Finset.mem_filter.mp h).1 : i∈tops G C)).2.2
          exact .next nt ⟨kind,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,pin⟩⟩ route
    have keep : Kept G C (n+t) := by
      intro i hi e
      have eq : i=t := by omega
      subst i
      exact GateOp.noConfusion ((Finset.mem_filter.mp top).2.1.symm.trans (Finset.mem_filter.mp hi).2.1)
    obtain ⟨i,e,_,_,term,lift⟩ := walk path keep
    have eq : i=t := by omega
    subst i
    have ht := term (Finset.mem_filter.mp top).2.2
    exact ⟨ht,lift _ (.stop ht)⟩
  · rintro ⟨_,route⟩
    have pass {a b} (h : MixerRoute n G C m a b) :
        Influence n C m (n+a) → Influence n C m (n+b) := by
      induction h with
      | stop => exact id
      | next _ edge _ ih =>
        obtain ⟨bound,pin⟩ := Finset.mem_filter.mp edge.2
        exact fun hp => ih (.step hp (Finset.mem_range.mp bound) pin)
    exact pass route .source

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
