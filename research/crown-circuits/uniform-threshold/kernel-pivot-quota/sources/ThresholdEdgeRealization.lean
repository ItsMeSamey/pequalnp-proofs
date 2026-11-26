import ThresholdSimpleIncidence
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction
namespace ThresholdSimpleIncidence

abbrev pinEmbedding {C : Circuit} {n} (L : Layout C n) :
    {v : T2OrPartition.Id C // v∈vertices L} ↪ Fin C.gates.length := Function.Embedding.subtype _

theorem edge_realized {C : Circuit} {n} (L : Layout C n)
    (card : ∀ e, (endpoints L e).card=2)
    {a b : {v : T2OrPartition.Id C // v∈vertices L}} (adj : (graph L).Adj a b) :
    ∃ e, endpoints L e={pinEmbedding L a,pinEmbedding L b} := by
  obtain ⟨ne,e,ha,hb⟩ := adj
  have ab : pinEmbedding L a ≠ pinEmbedding L b := fun h => ne ((pinEmbedding L).injective h)
  refine ⟨e,(Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · exact Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
  · change (endpoints L e).card ≤ ({pinEmbedding L a,pinEmbedding L b} : Finset _).card
    rw [card,Finset.card_pair_eq_two_iff.mpr ab]

end ThresholdSimpleIncidence
