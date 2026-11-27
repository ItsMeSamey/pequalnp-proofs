import Graph18272Bridge
import Q0Routes

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4186_aux
open scoped BigOperators

private theorem exists_minimum {n : ℕ} (H : SimpleGraph (Fin n)) :
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

/-- Combine a minimum cover of the star edges with one cover for each centreless top.
Residual edge families and local vertex covers can overlap. -/
theorem cover_union {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C)
    (edges : ℕ → Finset (Sym2 (Fin n))) (d : ℕ → ℕ)
    (residual : Ustar G C ⊆ (centreless G C).biUnion edges)
    (cost : (∑ t ∈ centreless G C, d t) ≤ (junk G C).card)
    (localCover : ∀ t ∈ centreless G C, ∃ V : Finset (Fin n),
      (∀ u v, s(u,v) ∈ edges t → u ∈ V ∨ v ∈ V) ∧ V.card + (edges t).card ≤ d t + 2) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card := by
  classical
  let T := centreless G C
  let U := Ustar G C
  have chooseCover (t : ℕ) : ∃ V : Finset (Fin n), t ∈ T →
      (∀ u v, s(u,v) ∈ edges t → u ∈ V ∨ v ∈ V) ∧ V.card + (edges t).card ≤ d t + 2 := by
    by_cases ht : t ∈ T
    · obtain ⟨V, hV⟩ := localCover t ht
      exact ⟨V, fun _ => hV⟩
    · exact ⟨∅, fun h => (ht h).elim⟩
  choose V hV using chooseCover
  let R := T.biUnion V
  obtain ⟨K, hK⟩ := exists_minimum (G.deleteEdges (↑U : Set (Sym2 (Fin n))))
  have hsize := (S4183.main n G C four edge least form).2 K hK
  refine ⟨K ∪ R, ?_, ?_⟩
  · intro u v huv
    by_cases he : s(u,v) ∈ U
    · obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp (residual he)
      rcases (hV t ht).1 u v het with hu | hv
      · exact Or.inl (Finset.mem_union_right K (Finset.mem_biUnion.mpr ⟨t,ht,hu⟩))
      · exact Or.inr (Finset.mem_union_right K (Finset.mem_biUnion.mpr ⟨t,ht,hv⟩))
    · have hd : (G.deleteEdges (↑U : Set (Sym2 (Fin n)))).Adj u v :=
        SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
      rcases hK.1 hd with hu | hv
      · exact Or.inl (Finset.mem_union_left R hu)
      · exact Or.inr (Finset.mem_union_left R hv)
  · have hr : R.card ≤ ∑ t ∈ T, (V t).card := Finset.card_biUnion_le
    have hu : U.card ≤ ∑ t ∈ T, (edges t).card :=
      (Finset.card_le_card residual).trans Finset.card_biUnion_le
    have hlocal : R.card + U.card ≤ (junk G C).card + 2 * T.card := by
      calc
        R.card + U.card ≤ _ := Nat.add_le_add hr hu
        _ = ∑ t ∈ T, ((V t).card + (edges t).card) := (Finset.sum_add_distrib).symm
        _ ≤ ∑ t ∈ T, (d t + 2) := Finset.sum_le_sum (fun t ht => (hV t ht).2)
        _ = (∑ t ∈ T, d t) + 2 * T.card := by simp [Finset.sum_add_distrib, Nat.mul_comm]
        _ ≤ _ := Nat.add_le_add_right cost _
    have hUnion := Finset.card_union_le K R
    change (K ∪ R).card + U.card ≤ (tops G C \ centreless G C).card + 2*T.card + (junk G C).card
    omega

/-- Deterministic first-reader routes make the routed junk charges disjoint, without any
condition on the number of readers of an OR gate. -/
theorem routed_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (reader : ∀ d ∈ junk G C, ∀ a ∈ readers n C d, ∀ b ∈ readers n C d, a = b) :
    (∑ t ∈ centreless G C, (Q0.routedJunk n G C t).card) ≤ (junk G C).card := by
  classical
  have hd : ((centreless G C) : Set ℕ).PairwiseDisjoint (Q0.routedJunk n G C) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro d da db
    apply hab
    apply Q0Partition.end_unique (hs := (Q0.mem_routedJunk.mp da).2)
      (ht := (Q0.mem_routedJunk.mp db).2)
    intro i j k hj hk
    exact reader i hj.1 j hj.2 k hk.2
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro d hd'
  obtain ⟨_, _, hdt⟩ := Finset.mem_biUnion.mp hd'
  exact (Q0.mem_routedJunk.mp hdt).1

theorem cover_of_routed_local_covers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (reader : ∀ d ∈ junk G C, ∀ a ∈ readers n C d, ∀ b ∈ readers n C d, a = b)
    (ordinary : ∀ t ∈ tops G C, t ∉ centreless G C → ∀ u v : Fin n, G.Adj u v →
      PEqualNP.EdgeOwnership.gateVal n C t (PEqualNP.EdgeOwnership.pairInput u v) = true →
      s(u,v) ∈ starEdges G C)
    (localCover : ∀ t ∈ centreless G C, ∃ V : Finset (Fin n),
      (∀ u v, s(u,v) ∈ Ustar G C ∩ gammaE G C t → u ∈ V ∨ v ∈ V) ∧
      V.card + (Ustar G C ∩ gammaE G C t).card ≤ (Q0.routedJunk n G C t).card + 2) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      S.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card :=
  cover_union G C four edge least form _ _ (Q0.residual_gamma_cover least ordinary)
    (routed_cost G C reader) localCover

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
