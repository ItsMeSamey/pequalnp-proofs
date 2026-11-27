import DDMixerRoutes

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem influenced_top_route {m t : ℕ} (D : DoubleDirty G C m)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (ht : t ∈ tops G C) (path : Influence n C m (n+t)) :
    t ∈ centreless G C ∧ MixerRoute n G C m m t :=
  (top_affected_iff_route G C m D edge least form ht).mp path

theorem unique_influenced_top {m : ℕ} (D : DoubleDirty G C m)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) :
    ∃! t, t ∈ tops G C ∧ Influence n C m (n+t) := by
  obtain ⟨t,⟨ht,rt⟩,unique⟩ := affected_unique G C m D edge least form
  have top : t ∈ tops G C := (Finset.mem_filter.mp ht).1
  refine ⟨t,⟨top,(top_affected_iff_route G C m D edge least form top).mpr ⟨ht,rt⟩⟩,?_⟩
  rintro a ⟨ha,path⟩
  exact unique a (influenced_top_route D edge least form ha path)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
