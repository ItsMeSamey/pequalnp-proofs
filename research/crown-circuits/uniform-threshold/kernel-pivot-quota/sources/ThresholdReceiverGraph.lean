import ThresholdReceiverTwo
import ThresholdReceiverSimple
import ThresholdGoodCount
namespace ThresholdSecondaryReceivers
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition
open ThresholdSimpleIncidence T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdRegularSource
def edgeFamily (C : Circuit) (n : Nat) (H : Finset (Id C)) :=
  (good C n H).image (signature C n)

theorem receiver_graph {n out : Nat} {gs : List ResidualSurplus.Raw}
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) (hn : 2≤n)
    (H : Finset (Id (source gs out))) (hub : H⊆ThresholdSharedPartition.hubs (source gs out) n)
    (common : ∀ u∈H, ∀ v∈H, u≠v → ∃ z x y, x≠y ∧
       u∈endpoints (layout n gs out M.eligible) x ∧ z∈endpoints (layout n gs out M.eligible) x ∧
       v∈endpoints (layout n gs out M.eligible) y ∧ endpoints (layout n gs out M.eligible) y⊆{v,z}) :
    let C := source gs out
    (edgeFamily C n H).card=(good C n H).card ∧
      edgeFamily C n H⊆(receivers C n H).powersetCard 2 := by
  let C := source gs out
  let L := layout n gs out M.eligible
  obtain ⟨inner,_,_⟩ := regular_inputs n gs out M.eligible reg
  refine ⟨Finset.card_image_of_injOn (signatures_injective M reg H common),?_⟩
  intro e he
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
  exact Finset.mem_powersetCard.mpr ⟨fun j hj => Finset.mem_biUnion.mpr ⟨u,hu,hj⟩,
    signature_two L inner M hn H hub u hu⟩
end ThresholdSecondaryReceivers
