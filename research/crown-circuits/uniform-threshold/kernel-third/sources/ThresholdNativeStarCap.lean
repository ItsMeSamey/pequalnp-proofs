import ThresholdNativeStarSaving
namespace ThresholdNativeStarSaving
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus T2OrPartition
open T2SoleOrSplice T2RegularOrDelete T2CubeDeletion ThresholdOrExtraction ThresholdRegularSource
open ThresholdStarRawSlots ThresholdSharedPartition ThresholdSharedOrBudget ThresholdSharedFlow
theorem regular_star_cap {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs)
    (u : Id (source gs out)) (hu : u∈hubs (source gs out) n) :
    let L := layout n gs out M.eligible
    (ThresholdHubDegrees.raws L u).card+(ThresholdHubDegrees.after L u).card+2*n≤
      (source gs out).size+3 := by
  classical
  intro L
  let k := (ThresholdHubDegrees.raws L u).card
  let t := (ThresholdHubDegrees.after L u).card
  change k+t+2*n≤_
  by_cases hk : 2≤k
  · obtain ⟨D,dm,dc,price⟩ := star_saving hn M reg u hu hk
    have floor := ThresholdGlobalGlue.original_or_floor D dm dc
    have gates : ThresholdOrGroups.ors D.gates≤D.size := List.countP_le_length
    change D.size+(2*n-k)+t+1≤_ at price
    change 2*k-4≤_ at floor
    omega
  · have sub : ThresholdHubDegrees.after L u⊆hubs (source gs out) n := Finset.filter_subset _ _
    have ht := Finset.card_le_card sub
    have small := List.toFinset_card_le (sharedOrs (source gs out) n)
    have budget := regular_shared_budget M reg
    change t≤(hubs (source gs out) n).card at ht
    change (hubs (source gs out) n).card≤_ at small
    omega
#print axioms regular_star_cap
end ThresholdNativeStarSaving
