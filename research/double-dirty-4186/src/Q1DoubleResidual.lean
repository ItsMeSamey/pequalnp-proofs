import Q1DoubleEndpoint
import Q1DoubleOwned
import Q1DoubleAffected

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux

theorem originalOwnership {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (D : DoubleDirty G C m) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) :
    ∃ owned : ℕ → Finset (Sym2 (Fin n)),
      (∀ h e, e ∈ owned h → e ∈ Ustar G C ∧ h ∈ centreless G C ∧ e ∈ gammaE G C h) ∧
      ((centreless G C) : Set ℕ).PairwiseDisjoint owned ∧
      (centreless G C).biUnion owned = Ustar G C ∧
      (∑ h ∈ centreless G C, (owned h).card) = (Ustar G C).card := by
  classical
  have all : Ustar G C ⊆ (centreless G C).biUnion (fun t => Ustar G C ∩ gammaE G C t) := Q0.residual_gamma_cover least (by
    intro t ht nc u v _ hv
    exact noncentreless_accepted_star least.1 form D (Finset.mem_sdiff.mpr ⟨ht,nc⟩) u v hv)
  apply owned_partition
  intro e he
  obtain ⟨t, ht, both⟩ := Finset.mem_biUnion.mp (all he)
  exact ⟨t, ht, (Finset.mem_inter.mp both).2⟩

theorem complete_of_small_residual {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (D : DoubleDirty G C m) (four : NoFourCycle G)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (small : (Ustar G C).card ≤ 2) : Positive G C := by
  obtain ⟨h, hh, _⟩ := affected_exists D edge least
  obtain ⟨a, ha, _⟩ := D.pins 0
  have cpos : 0 < (centreless G C).card := Finset.card_pos.mpr ⟨h,hh⟩
  have jpos : 0 < (junk G C).card := Finset.card_pos.mpr ⟨a,ha⟩
  exact fromAmple G C four edge least form (by simp [D.exception]) (by omega)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
