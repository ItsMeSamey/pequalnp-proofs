import Graph18272Bridge
import Q0Endpoint

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

private lemma existsMinCover {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∃ K : Finset (Fin n), IsMinCover H K := by
  classical
  let P := fun k : ℕ => ∃ K : Finset (Fin n), H.IsVertexCover (K : Set (Fin n)) ∧ K.card = k
  have ex : ∃ k, P k :=
    ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, by simp, rfl⟩
  obtain ⟨K, covered, hcard⟩ := Nat.find_spec ex
  refine ⟨K, covered, ?_⟩
  intro T hT
  rw [hcard]
  exact Nat.find_min' ex (show P T.card from ⟨T, hT, rfl⟩)

theorem coverBound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card ≤ (tops G C \ centreless G C).card + (Ustar G C).card := by
  classical
  let U := Ustar G C
  obtain ⟨K, hK⟩ := existsMinCover (G.deleteEdges (↑U : Set (Sym2 (Fin n))))
  have hsize := (S4183.main n G C four edge least form).2 K hK
  let R := U.image (fun e : Sym2 (Fin n) => e.out.1)
  refine ⟨K ∪ R, ?_, ?_⟩
  · intro u v huv
    by_cases he : s(u, v) ∈ U
    · have hp : (s(u, v)).out.1 ∈ R := Finset.mem_image.mpr ⟨s(u, v), he, rfl⟩
      rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(u, v)) with hu | hv
      · exact Or.inl (Finset.mem_union_right K (hu ▸ hp))
      · exact Or.inr (Finset.mem_union_right K (hv ▸ hp))
    · have hd : (G.deleteEdges (↑U : Set (Sym2 (Fin n)))).Adj u v :=
        SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
      rcases hK.1 hd with hu | hv
      · exact Or.inl (Finset.mem_union_left R hu)
      · exact Or.inr (Finset.mem_union_left R hv)
  · exact (Finset.card_union_le K R).trans (Nat.add_le_add hsize Finset.card_image_le)

theorem endpointOfCharge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (charge : 2 * (Ustar G C).card ≤ (junk G C).card + 2 * (centreless G C).card) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card :=
  endpoint G C charge (coverBound G C four edge least form)

end PEqualNP.Outside.L_meta_4186_aux.Q0
