import Q0FactorSemantics

namespace PEqualNP.Outside.L_meta_4186_aux.Q0.Factor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux.S4183.S98

theorem pinRules {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (hq : (orN G C \ lam G C).card = 0)
    (hg : g ∈ junk G C) : PinRules G C g := by
  classical
  obtain ⟨reader, out, _⟩ := main_real n G C edge least form
  constructor
  · intro j hj hn w hw k hk he
    obtain ⟨hkr, _, hkb⟩ := Finset.mem_filter.mp hk
    have hr : j ∈ readers n C k := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, he ▸ hw⟩
    have ne : n+k ≠ C.output := by
      intro e
      have sub : C.output-n = k := by omega
      rw [sub] at out
      simpa [out] using hr
    obtain ⟨r, onlyReader, hor, hb⟩ := reader k (Finset.mem_range.mp hkr) hkb ne
    rw [onlyReader, Finset.mem_singleton] at hr
    subst r
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hor, hb⟩)
  · intro j hj hn hor w hw path
    have hjN : j ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hor, fun h =>
      hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hor, h⟩)⟩
    have hL : j ∈ lam G C := by
      by_contra hm
      have hh := Finset.mem_sdiff.mpr ⟨hjN, hm⟩
      rw [Finset.card_eq_zero.mp hq] at hh
      simpa using hh
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hL
    have nonempty : (orIn n C w).Nonempty := by
      rcases reader_pin least.1 hj hw with he | he
      · simpa only [he] using h0
      · simpa only [he] using h1
    have empty : orIn n C w = ∅ := by
      cases path with
      | source => exact and_empty_support ((S4183.junk_iff G C g).mp hg).2.1
      | step _ _ hand _ => exact and_empty_support hand
    simpa [empty] using nonempty

end PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
