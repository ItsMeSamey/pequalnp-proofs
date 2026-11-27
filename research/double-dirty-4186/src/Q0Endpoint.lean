import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem endpoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (charge : 2 * (Ustar G C).card ≤ (junk G C).card + 2 * (centreless G C).card)
    (coverBound : ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card ≤ (tops G C \ centreless G C).card + (Ustar G C).card) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  obtain ⟨S, hS, bound⟩ := coverBound
  exact ⟨S, hS, by omega⟩

end PEqualNP.Outside.L_meta_4186_aux.Q0
