import Q0FromUnique
import Q0FactorActual

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem complete {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (hq : (orN G C \ lam G C).card = 0) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card :=
  from_unique G C four edge least form hq (Factor.unique_reader G C edge least form hq)

end PEqualNP.Outside.L_meta_4186_aux.Q0
