import Q1PureBase
import Q0FactorPinRules

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98

theorem pinRules {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (pure : NoDirtyOr G C)
    (hg : g ∈ junk G C) : PinRules G C g := by
  classical
  obtain ⟨reader, out, _⟩ := main_real n G C edge least form
  have clean {i j : ℕ} (hi : i < C.gates.length) (hb : BelowF G C i)
      (hj : j < C.gates.length) (pin : n+i ∈ (gateAt C j).inputs) : j ∈ orT G C := by
    have hr : j ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, pin⟩
    have ne : n+i ≠ C.output := by
      intro e
      have ix : C.output-n = i := by omega
      rw [ix] at out
      simpa [out] using hr
    obtain ⟨r, singleton, hop, below⟩ := reader i hi hb ne
    rw [singleton, Finset.mem_singleton] at hr
    subst r
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, below⟩
  constructor
  · intro j hj hn w hw i hi eq
    obtain ⟨hl, _, hb⟩ := Finset.mem_filter.mp hi
    exact hn (clean (Finset.mem_range.mp hl) hb hj (eq ▸ hw))
  · intro j hj hn hor w hw path
    have ends : ∃ i, w = n+i ∧ i < C.gates.length ∧ (gateAt C i).op = .and := by
      cases path with
      | source =>
        obtain ⟨bound, op, _⟩ := (S4183.junk_iff G C g).mp hg
        exact ⟨g,rfl,bound,op⟩
      | step _ bound op _ => exact ⟨_,rfl,bound,op⟩
    obtain ⟨i, rfl, bound, op⟩ := ends
    by_cases hb : BelowF G C i
    · exact hn (clean bound hb hj hw)
    · exact (pure ((S4183.junk_iff G C i).mpr ⟨bound,op,hb⟩) hj hw) hor

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
