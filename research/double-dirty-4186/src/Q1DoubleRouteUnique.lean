import Q1DoubleAffected

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem downstream_reader {m i r : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (mi : m ≤ i) (hi : i = m ∨ i ∈ junk G C) (rd : r ∈ readers n C i) :
    i < r ∧ (gateAt C r).op = GateOp.and := by
  obtain ⟨hr',hin⟩ := Finset.mem_filter.mp rd
  have hr := Finset.mem_range.mp hr'
  have lt := ao.2.1 r hr _ hin
  refine ⟨by omega, (ao.1 _ (S4183.S90.gateAt_mem hr)).resolve_right ?_⟩
  intro hor
  rcases hi with rfl | hj
  · exact no_mixer_or D ao hr hin hor
  · have er := dirty_or_eq D ao hj hr hin hor
    omega

theorem route_unique {m : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (fanout : ∀ i, m ≤ i → (i = m ∨ i ∈ junk G C) → ∀ r ∈ readers n C i,
      (gateAt C r).op = GateOp.and → ∀ s ∈ readers n C i,
        (gateAt C s).op = GateOp.and → r = s)
    {i a b : ℕ} (mi : m ≤ i) (ra : MixerRoute n G C m i a)
    (rb : MixerRoute n G C m i b) : a = b := by
  induction ra generalizing b with
  | stop h =>
    cases rb with
    | stop => rfl
    | next hn _ _ => exact (hn h).elim
  | @next i r t hn hrd tail ih =>
    cases rb with
    | stop h => exact (hn h).elim
    | next _ hsd rest =>
      have hr := downstream_reader D ao mi hrd.1 hrd.2
      have hs := downstream_reader D ao mi hsd.1 hsd.2
      obtain rfl := fanout i mi hrd.1 r hrd.2 hr.2 _ hsd.2 hs.2
      exact ih (by omega) rest

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
