import Q0CoverBound
import Q1DoubleTopology

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

def Positive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
    S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card

def DoubleDirtyCase : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
    (orN G C \ lam G C).card = 1 →
    (∃ e ∈ orN G C \ lam G C, ∃ a ∈ junk G C, ∃ b ∈ junk G C,
      (gateAt C e).inputs = [n+a,n+b]) → Positive G C

theorem doubleDirty_of_pins {n m a b : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (q : (orN G C \ lam G C).card = 1) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ junk G C) (hb : b ∈ junk G C) (pins : (gateAt C m).inputs = [n+a,n+b]) :
    DoubleDirty G C m := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp q
  rw [hk, Finset.mem_singleton] at hm
  subst k
  refine ⟨hk, ?_⟩
  intro i
  fin_cases i
  · exact ⟨a, ha, by simp [opnd,pins]⟩
  · exact ⟨b, hb, by simp [opnd,pins]⟩

theorem fromAmple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (one : (orN G C \ lam G C).card = 1)
    (ample : 2 * (Ustar G C).card ≤ 2 * (centreless G C).card + (junk G C).card + 1) :
    Positive G C := by
  obtain ⟨S, covers, size⟩ := Q0.coverBound G C four edge least form
  exact ⟨S, covers, by omega⟩

theorem iffCoverSaving {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (one : (orN G C \ lam G C).card = 1)
    (tight : 2 * (centreless G C).card + (junk G C).card + 1 < 2 * (Ustar G C).card) :
    Positive G C ↔ ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (2 * (Ustar G C).card - (2 * (centreless G C).card + (junk G C).card + 1)) ≤
        (tops G C \ centreless G C).card + (Ustar G C).card := by
  constructor <;> rintro ⟨S, cover, bound⟩ <;> exact ⟨S, cover, by omega⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
