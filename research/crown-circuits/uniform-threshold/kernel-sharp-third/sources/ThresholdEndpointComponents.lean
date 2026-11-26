import ThresholdEndpointBound

namespace ThresholdEndpointBound
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdGraphCounts

theorem endpoint_components {C : Circuit} {n : Nat} (L : Layout C n)
    (two : ∀ w, (endpoints L w).card = 2) (inj : Function.Injective (endpoints L)) :
    2*Nat.card (graph L).ConnectedComponent ≤ (vertices L).card := by
  classical
  let G := graph L
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let B := fun c : G.ConnectedComponent =>
    Finset.univ.filter (fun v : Vtx L => G.connectedComponentMk v = c)
  have jmin (c : G.ConnectedComponent) : 2 ≤ (B c).card := by
    refine SimpleGraph.ConnectedComponent.ind (fun v => ?_) c
    obtain ⟨w,h⟩ := (G.degree_pos_iff_exists_adj v).mp
      (ThresholdGraphCounts.degree_pos L v two inj)
    have sub : ({v,w} : Finset (Vtx L)) ⊆ B (G.connectedComponentMk v) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | hw
      · simp [B]
      · have e : a = w := Finset.mem_singleton.mp hw
        subst a
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h).symm⟩
    simpa [h.ne] using Finset.card_le_card sub
  have fiber (f : Vtx L → Nat) : (∑ c, ∑ x ∈ B c, f x) = ∑ x, f x := by
    exact Finset.sum_fiberwise_of_maps_to (g := G.connectedComponentMk)
      (fun i (_ : i ∈ (Finset.univ : Finset (Vtx L))) => Finset.mem_univ _) f
  have total : (∑ c, (B c).card) = Fintype.card (Vtx L) := by
    simpa using fiber (fun _ => 1)
  have enough := Finset.sum_le_sum (s := Finset.univ) (fun c _ => jmin c)
  change 2*Nat.card G.ConnectedComponent ≤ (vertices L).card
  simpa [total,Nat.card_eq_fintype_card,Vtx,Nat.mul_comm] using enough

end ThresholdEndpointBound
