import ThresholdReceiverShield
import ThresholdC4Missing
namespace ThresholdReceiverCollision
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete T2OrPartition ThresholdSimpleIncidence
open ThresholdSharedFlow ThresholdStarBypass ResidualSurplus ThresholdSecondaryReceivers
open ThresholdC4Missing
theorem union_injective {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (H : Finset (Id (source gs out))) :
    let C := source gs out
    let L := layout n gs out M.eligible
    let A := (Finset.univ : Finset (Fin n)).image (endpoints L)
    ∀ p∈A, ∀ q∈A, p⊆good C n H → support (signature C n) p=support (signature C n) q → p=q := by
  intro C L A p hp q hq gp same
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hq
  by_cases eq : x=y
  · rw [eq]
  exfalso
  apply ThresholdReceiverShield.cannot_add_shield M reg x y eq (endpoints L y) (fun _ h => h)
  · intro u uy i iu s xs
    have hit : i∈support (signature C n) (endpoints L y) := Finset.mem_biUnion.mpr ⟨u,uy,iu⟩
    rw [←same] at hit
    obtain ⟨v,vx,iv⟩ := Finset.mem_biUnion.mp hit
    have hot := (receiver_later L (gp vx) iv).2
    exact ThresholdSharedPairErase.probe_le_actual L v
      (fun k => (C.wires (vector s)).getD k false)
      (fun k => (L.atIndex k).eval _ (by simp [vector])) (endpoint_hot L s x v xs vx) _ hot
  · exact fun _ h nh => False.elim (nh h)
end ThresholdReceiverCollision
