import ThresholdComponentEdges
import ThresholdGraphCounts

namespace ThresholdEndpointBound
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdGraphCounts

theorem endpoint_edges {C : Circuit} {n Δ : Nat} (L : Layout C n)
    (two : ∀ w, (endpoints L w).card = 2) (inj : Function.Injective (endpoints L))
    (bound : ∀ v : Vtx L, (rawAt L v).card ≤ Δ) :
    2*n ≤ 2*Nat.card (graph L).ConnectedComponent +
      ((vertices L).card - 2*Nat.card (graph L).ConnectedComponent)*(Δ+2) := by
  classical
  letI : Fintype (graph L).ConnectedComponent := Fintype.ofFinite _
  have neighbors (v : Vtx L) := ((graph L).degree_pos_iff_exists_adj v).mp
    (ThresholdGraphCounts.degree_pos L v two inj)
  have degrees (v : Vtx L) : (graph L).degree v ≤ Δ := by
    rw [degree_eq_raw L v two inj]
    exact bound v
  have h := ThresholdComponentEdges.component_edges (graph L) neighbors degrees
  rw [graph_edge_card L two inj] at h
  simpa [Nat.card_eq_fintype_card,Vtx] using h

end ThresholdEndpointBound
