import ThresholdRegularWedgeLedger
namespace ThresholdNativeRowSelection
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSharedPartition ThresholdHighComponents
open ThresholdEffectiveColumns ThresholdSecondaryReceivers ThresholdWarmSimple ThresholdPurityPins
open ThresholdFanoutBudget ThresholdFlowSum ThresholdSharedFlow ThresholdNativeColumnCharge
open ThresholdAmbientEffectiveGraph
open scoped BigOperators
theorem selected_moments {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
    (room : let L := layout n gs out minim.eligible
      9*trimCost L < (high L).card^2)
    (space : let L := layout n gs out minim.eligible
      let h := hubs (source gs out) n
      2*((h \ high L).card+2*(trimCost L).sqrt+1)≤h.card) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let H := high L
    let h := hubs C n
    let m := (trimCost L).sqrt
    let low := (h \ H).card
    let holes := (inner L H).card
    ∃ R⊆retained L, ∃ t A D : Nat,
      let w := (R.biUnion (effective L minim)).card
      let g := R.card
      let coarse := holes+2*H.card*low
      H.card≤g+(impure L H).card+deltaO L+3*(andIds C).length+4*t+m+2*(receivers C n H).card ∧
      t.choose 2≤ThresholdHubMissing.M L+1 ∧
      2*(((h.card-(low+4*m):Nat):ℤ)*(w:ℤ)+(holes:ℤ))≤ThresholdHubFine.budget n C.size ∧
      A^2≤g*(A+D+6*coarse) ∧ 2*D^2≤w^2*(4*coarse+D) ∧
      2*D^2≤w^2*(4*(holes+4*(A+D)+4*g)+D) ∧ (2*g)^2≤w*(2*(A+D)+2*g) := by
  intro C L H h m low holes
  obtain ⟨R,sub,t,_,two,inj,_,row,choose,col⟩ := selected_columns hn minim reg room space
  obtain ⟨A,D,adj,dc,df,_,wedge⟩ := wedge_bounds (by omega) minim reg R sub two inj
  exact ⟨R,sub,t,A,D,row,choose,col,adj,dc,df,wedge⟩
end ThresholdNativeRowSelection
